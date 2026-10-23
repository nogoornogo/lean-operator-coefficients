import Math.RepresentationTheory.Relations.RelationQuotient

/-! Local coinvariants classify invariant functionals, equivariantly for an
arbitrary commuting residual action. No averaging or semisimplicity is used. -/
namespace Math.LocalCoinvariantHom
set_option autoImplicit false
noncomputable section
open Representation

variable {k G H U W : Type*} [Field k] [Group G] [Group H]
  [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
  (localAction : Representation k G U) (residual : Representation k H U)
  (target : Representation k H W)
  (commutes : ∀ g h u, localAction g (residual h u) = residual h (localAction g u))

def relation (p : G × U) : U := localAction p.1 p.2 - p.2
abbrev relations := RelationQuotient.relations (k := k) (relation localAction)

include commutes in
theorem stable : ∀ h, relations localAction ≤ (relations localAction).comap (residual h) := by
  apply RelationQuotient.relations_stable
  intro h p
  have he : residual h (relation localAction p) =
      relation localAction (p.1, residual h p.2) := by
    simp only [relation, map_sub]
    rw [commutes]
  rw [he]
  exact Submodule.subset_span ⟨_, rfl⟩

abbrev quotient := residual.quotient (relations localAction) (stable localAction residual commutes)

def invariantHom : Submodule k (IntertwiningMap residual target) where
  carrier := {f | ∀ g u, f (localAction g u) = f u}
  zero_mem' := by intro g u; rfl
  add_mem' := by intro f q hf hq g u; change f _ + q _ = f _ + q _; rw [hf, hq]
  smul_mem' := by intro z f hf g u; change z • f _ = z • f _; rw [hf]

theorem invariant_eq_vanishing : invariantHom localAction residual target =
    RelationQuotient.vanishing residual target (relations localAction) := by
  apply Submodule.ext
  intro f
  rw [RelationQuotient.vanish_relations_iff]
  change (∀ g u, f (localAction g u) = f u) ↔ ∀ p : G × U, f (relation localAction p) = 0
  simp only [relation, map_sub, sub_eq_zero]
  constructor
  · intro hf p; exact hf p.1 p.2
  · intro hf g u; exact hf (g,u)

/-- A constructed quotient, not a local spanning-dictionary premise. -/
def equiv : invariantHom localAction residual target ≃ₗ[k]
    IntertwiningMap (quotient localAction residual commutes) target :=
  (LinearEquiv.ofEq _ _ (invariant_eq_vanishing localAction residual target)).trans
    (RelationQuotient.equiv residual target (relations localAction)
      (stable localAction residual commutes))

@[simp] theorem equiv_mk (f : invariantHom localAction residual target) (u : U) :
    equiv localAction residual target commutes f ((relations localAction).mkQ u) = f.val u := rfl

@[simp] theorem equiv_symm_apply
    (f : IntertwiningMap (quotient localAction residual commutes) target) (u : U) :
    ((equiv localAction residual target commutes).symm f).val u =
      f ((relations localAction).mkQ u) := rfl

theorem forbidden_iff : (∀ f : invariantHom localAction residual target, f = 0) ↔
    ∀ q : IntertwiningMap (quotient localAction residual commutes) target, q = 0 := by
  constructor
  · intro hz q
    exact (equiv localAction residual target commutes).symm.injective
      ((hz _).trans (equiv localAction residual target commutes).symm.map_zero.symm)
  · intro hz f
    exact (equiv localAction residual target commutes).injective
      ((hz _).trans (equiv localAction residual target commutes).map_zero.symm)

theorem nonzero_iff : (∃ f : invariantHom localAction residual target, f ≠ 0) ↔
    ∃ q : IntertwiningMap (quotient localAction residual commutes) target, q ≠ 0 := by
  simpa only [not_forall, not_not] using not_congr
    (forbidden_iff localAction residual target commutes)

section Exchange
variable (f : IntertwiningMap residual residual)
  (compatible : ∀ g u, f (localAction g u) = localAction g (f u))

include compatible in
theorem map_relations : relations localAction ≤ (relations localAction).comap f.toLinearMap := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g,u⟩,rfl⟩
  change f (localAction g u - u) ∈ relations localAction
  rw [map_sub, compatible]
  exact Submodule.subset_span ⟨(g,f u),rfl⟩

/-- Local-compatible exchange maps descend without choosing a local basis. -/
def descendExchange : IntertwiningMap (quotient localAction residual commutes)
    (quotient localAction residual commutes) where
  toLinearMap := (relations localAction).mapQ (relations localAction) f.toLinearMap
    (map_relations localAction residual f compatible)
  isIntertwining' h := by
    apply LinearMap.ext
    intro u
    obtain ⟨v,rfl⟩ := (relations localAction).mkQ_surjective u
    change (relations localAction).mkQ (f (residual h v)) =
      (relations localAction).mkQ (residual h (f v))
    rw [IntertwiningMap.isIntertwining]

@[simp] theorem descendExchange_mk (u : U) :
    descendExchange localAction residual commutes f compatible ((relations localAction).mkQ u) =
      (relations localAction).mkQ (f u) := rfl

end Exchange

end
end Math.LocalCoinvariantHom
