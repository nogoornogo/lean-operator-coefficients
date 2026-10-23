import Math.RepresentationTheory.Jets.DerivativeInterface
import Math.RepresentationTheory.Protection.ScalarProhibitionNecessity
import Math.RepresentationTheory.Decomposition.CommonIrreducible

/-! Necessary prohibition conditions on actual derivative relation quotients.
No raw-source support, invariant complement or grading premise is inferred. -/
namespace Math.DerivativeProhibition
set_option autoImplicit false
noncomputable section
open Representation

variable {H U W : Type*} [Group H] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup W] [Module ℂ W] (P : DerivativeInterface.Input H U)

def Forbids : Prop := SelectionCriteria.Forbidden P.Coefficient
def Allows : Prop := SelectionCriteria.Allowed P.Coefficient

theorem forbids_iff : Forbids P ↔
    ∀ f : IntertwiningMap P.residual (trivial ℂ H ℂ), f = 0 := P.forbidden_iff

theorem allows_iff : Allows P ↔
    ∃ f : IntertwiningMap P.residual (trivial ℂ H ℂ), f ≠ 0 := P.nonzero_iff

theorem zero_source_forbids [Subsingleton P.Source] : Forbids P :=
  (forbids_iff P).mpr (ScalarProhibitionNecessity.zero_carrier_forbidden P.residual)

theorem scalar_iff [Nontrivial P.Source] (z : H → ℂ)
    (hs : ∀ g q, P.residual g q = z g • q) :
    Forbids P ↔ ∃ g, z g ≠ 1 :=
  (forbids_iff P).trans (ScalarProhibitionNecessity.forbidden_iff_detect P.residual z hs)

theorem scalar_supported_iff (z : H → ℂ)
    (hs : ∀ g q, P.residual g q = z g • q) :
    Forbids P ↔ (Nontrivial P.Source → ∃ g, z g ≠ 1) := by
  constructor
  · intro hf hn
    let := hn
    exact (scalar_iff P z hs).mp hf
  · intro h
    rcases subsingleton_or_nontrivial P.Source with hz | hn
    · let := hz
      exact zero_source_forbids P
    · let := hn
      exact (scalar_iff P z hs).mpr (h hn)

theorem quotient_scalar (z : H → ℂ) (hs : ∀ g u, P.action g u = z g • u)
    (g : H) (q : P.Source) : P.residual g q = z g • q := by
  obtain ⟨u,rfl⟩ := P.relations.mkQ_surjective q
  change P.projection (P.action g u) = z g • P.projection u
  rw [hs,map_smul]

theorem ambient_scalar_supported_iff (z : H → ℂ)
    (hs : ∀ g u, P.action g u = z g • u) :
    Forbids P ↔ (Nontrivial P.Source → ∃ g, z g ≠ 1) :=
  scalar_supported_iff P z (quotient_scalar P z hs)

theorem no_shared_iff (hr : IsSemisimpleRepresentation P.residual) :
    Forbids P ↔ ¬ CommonIrreducible.Shares P.residual (trivial ℂ H ℂ) :=
  (forbids_iff P).trans (CommonIrreducible.all_zero_iff _ _ hr)

theorem shared_defeats (hr : IsSemisimpleRepresentation P.residual)
    (hc : CommonIrreducible.Shares P.residual (trivial ℂ H ℂ)) : ¬ Forbids P :=
  fun hf => (no_shared_iff P hr).mp hf hc

theorem transport (Q : DerivativeInterface.Input H W)
    (e : P.Coefficient ≃ₗ[ℂ] Q.Coefficient) : Forbids P ↔ Forbids Q :=
  (SelectionCriteria.ofEquiv e).forbidden

section Relations
variable (T : Submodule ℂ U) (hT : ∀ g, T ≤ T.comap (P.action g))

def extend : DerivativeInterface.Input H U where
  action := P.action
  relations := P.relations ⊔ T
  stable g := by
    apply sup_le
    · intro u hu
      exact Submodule.mem_sup_left (P.stable g hu)
    · intro u hu
      exact Submodule.mem_sup_right (hT g hu)

def forgetRelations : (extend P T hT).Coefficient →ₗ[ℂ] P.Coefficient where
  toFun f := ⟨f.val, fun _ hp => f.property (Submodule.mem_sup_left hp)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem forget_injective : Function.Injective (forgetRelations P T hT) := by
  intro f g h
  exact Subtype.ext (congrArg (fun q : P.Coefficient => q.val) h)

theorem forget_evaluation (f : (extend P T hT).Coefficient) (u : U) :
    (forgetRelations P T hT f).val u = f.val u := rfl

theorem forbids_extend (hf : Forbids P) : Forbids (extend P T hT) := by
  intro f
  apply forget_injective P T hT
  exact (hf (forgetRelations P T hT f)).trans (map_zero (forgetRelations P T hT)).symm

theorem allows_before (ha : Allows (extend P T hT)) : Allows P := by
  obtain ⟨f,hf⟩ := ha
  refine ⟨forgetRelations P T hT f, fun hz => hf ?_⟩
  apply forget_injective P T hT
  rw [hz,map_zero]
end Relations

section Selected
variable (V : Submodule ℂ U) (hV : ∀ g, V ≤ V.comap (P.action g))

/-- Every global admissible coefficient vanishes on the requested source. -/
def TargetForbids : Prop := ∀ f : P.Coefficient, ∀ v : V, f.val v.val = 0

theorem target_iff_restrict_zero : TargetForbids P V ↔
    ∀ f : P.Coefficient, P.restrict V hV f = 0 := by
  constructor
  · intro h f
    apply Subtype.ext
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    exact h f v
  · intro h f v
    exact congrArg (fun q : (P.select V hV).Coefficient => q.val v) (h f)

theorem selected_forbids_target (h : Forbids (P.select V hV)) : TargetForbids P V :=
  (target_iff_restrict_zero P V hV).mpr (fun f => h (P.restrict V hV f))

theorem target_forbids_selected (he : Function.Surjective (P.restrict V hV))
    (h : TargetForbids P V) : Forbids (P.select V hV) := by
  intro f
  obtain ⟨g,rfl⟩ := he f
  exact (target_iff_restrict_zero P V hV).mp h g

theorem target_selected_iff (he : Function.Surjective (P.restrict V hV)) :
    TargetForbids P V ↔ Forbids (P.select V hV) :=
  ⟨target_forbids_selected P V hV he,selected_forbids_target P V hV⟩

theorem restriction_obstruction (h : TargetForbids P V)
    (ha : Allows (P.select V hV)) : ¬ Function.Surjective (P.restrict V hV) := by
  intro he
  obtain ⟨f,hf⟩ := ha
  exact hf (target_forbids_selected P V hV he h f)

theorem target_charge_detected [Nontrivial (P.select V hV).Source]
    (z : H → ℂ) (hs : ∀ g q, (P.select V hV).residual g q = z g • q)
    (he : Function.Surjective (P.restrict V hV)) (h : TargetForbids P V) :
    ∃ g, z g ≠ 1 :=
  (scalar_iff (P.select V hV) z hs).mp (target_forbids_selected P V hV he h)

theorem target_no_shared (hr : IsSemisimpleRepresentation (P.select V hV).residual)
    (he : Function.Surjective (P.restrict V hV)) (h : TargetForbids P V) :
    ¬ CommonIrreducible.Shares (P.select V hV).residual (trivial ℂ H ℂ) :=
  (no_shared_iff (P.select V hV) hr).mp (target_forbids_selected P V hV he h)
end Selected

section Family
variable {ι : Type*} {A : ι → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
  (family : ∀ i, DerivativeInterface.Input H (A i)) (s : ι → Prop)

def AllForbids : Prop := ∀ i, s i → Forbids (family i)

theorem all_scalar_supported_iff (z : ι → H → ℂ)
    (hs : ∀ i g q, (family i).residual g q = z i g • q) :
    AllForbids family s ↔ ∀ i, s i → Nontrivial (family i).Source → ∃ g, z i g ≠ 1 := by
  simp only [AllForbids,scalar_supported_iff _ _ (hs _)]
end Family

section ZeroGrade
variable {F B I : Type*} [Fintype I]
  (rhoF : Representation ℂ H (JetLinear.Field F))
  (rhoB : Representation ℂ H (JetLinear.Field B))
  (sigma : Representation ℂ H (JetDirections.Direction I))

theorem zero_grade_iff (n m : ℕ) :
    Forbids (DerivativeInterface.graded rhoF rhoB sigma n m 0) ↔
    SelectionCriteria.Forbidden (InvariantCoefficientTransport.Invariants
      (MixedJetSource.originalAction rhoF rhoB n m)) :=
  (SelectionCriteria.ofEquiv (DerivativeInterface.fromNonDerivative rhoF rhoB sigma n m)).forbidden.symm
end ZeroGrade

end
end Math.DerivativeProhibition
