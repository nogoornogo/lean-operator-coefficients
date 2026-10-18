import Math.RepresentationTheory.LocalCoinvariantHom

/-! Local invariant Hom descent for automorphism-covariant residual actions. -/
namespace Math.AutomorphismCovariantHom
set_option autoImplicit false
noncomputable section
open Representation

variable {k G H V W : Type*} [Field k] [Group G] [Group H]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- An ordinary linear residual action normalizing the local representation. -/
structure Action (localAction : Representation k G V) (alpha : H →* MulAut G) where
  residual : Representation k H V
  covariance : ∀ h g v, residual h (localAction g v) =
    localAction (alpha h g) (residual h v)

variable (a : Representation k G V) (alpha : H →* MulAut G) (A : Action a alpha)
  (t : Representation k H W)

/-- Normalization, rather than commutation, preserves local coinvariant relations. -/
theorem stable : ∀ h, LocalCoinvariantHom.relations a ≤
    (LocalCoinvariantHom.relations a).comap (A.residual h) := by
  apply RelationQuotient.relations_stable
  intro h p
  have he : A.residual h (LocalCoinvariantHom.relation a p) =
      LocalCoinvariantHom.relation a (alpha h p.1, A.residual h p.2) := by
    simp only [LocalCoinvariantHom.relation, map_sub, A.covariance]
  rw [he]
  exact Submodule.subset_span ⟨_, rfl⟩

abbrev quotient := A.residual.quotient (LocalCoinvariantHom.relations a) (stable a alpha A)

/-- Two-sided Hom descent; no dimension or semisimplicity input. -/
def equiv : LocalCoinvariantHom.invariantHom a A.residual t ≃ₗ[k]
    IntertwiningMap (quotient a alpha A) t :=
  (LinearEquiv.ofEq _ _ (LocalCoinvariantHom.invariant_eq_vanishing a A.residual t)).trans
    (RelationQuotient.equiv A.residual t (LocalCoinvariantHom.relations a) (stable a alpha A))

@[simp] theorem equiv_mk (f : LocalCoinvariantHom.invariantHom a A.residual t) (v : V) :
    equiv a alpha A t f ((LocalCoinvariantHom.relations a).mkQ v) = f.val v := rfl

/-- Prohibition is equivalent to vanishing of the constructed residual Hom. -/
theorem forbidden_iff :
    (∀ f : LocalCoinvariantHom.invariantHom a A.residual t, f = 0) ↔
    ∀ q : IntertwiningMap (quotient a alpha A) t, q = 0 := by
  let e := equiv a alpha A t
  constructor
  · intro hf q
    obtain ⟨f, rfl⟩ := e.surjective q
    rw [hf f, map_zero]
  · intro hq f
    apply e.injective
    exact (hq (e f)).trans (map_zero e).symm

/-- Noncommuting covariance control: an action normalizes itself by conjugation.
This generic control is not a protecting SU(6) model. -/
def conjugationControl (rho : Representation k G V) : Action rho (MulAut.conj : G →* MulAut G) where
  residual := rho
  covariance h g v := by
    change rho h (rho g v) = rho (h * g * h⁻¹) (rho h v)
    simp only [← Module.End.mul_apply, ← map_mul]
    simp

/-- A faithful self-normalizing action commutes precisely when the tested group
 elements commute; hence the covariant interface does not force commutation. -/
theorem conjugationControl_commutes_iff (rho : Representation k G V)
    (faithful : Function.Injective rho) (g h : G) :
    (∀ v, rho g (rho h v) = rho h (rho g v)) ↔ g * h = h * g := by
  constructor
  · intro hc
    apply faithful
    ext v
    simpa only [map_mul, Module.End.mul_apply] using hc v
  · intro hc v
    have he := congrArg rho hc
    simpa only [map_mul, Module.End.mul_apply] using
      congrArg (fun f : Module.End k V => f v) he

/-- The identity automorphism action recovers strict commutation. -/
theorem commutes_of_identity (ha : alpha = 1) (g : G) (h : H) (v : V) :
    a g (A.residual h v) = A.residual h (a g v) := by
  subst alpha
  exact (A.covariance h g v).symm

end
end Math.AutomorphismCovariantHom
