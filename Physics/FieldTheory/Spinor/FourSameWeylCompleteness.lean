import Physics.FieldTheory.Spinor.WeylSpinor
import Math.RepresentationTheory.Unitary.FourDoubletInvariant
import Math.RepresentationTheory.FiniteInvariantFactor

open Math

/-! Four same-chirality Weyl spinors have exactly two invariant coefficients. -/
namespace GUT.FourSameWeylCompleteness
set_option autoImplicit false
noncomputable section
open Representation FourDoubletInvariant
open scoped TensorProduct

def action (rightHanded : Bool) := if rightHanded then WeylSpinor.right else WeylSpinor.left
def representation (rightHanded : Bool) :=
  ((action rightHanded).tprod (action rightHanded)).tprod
    ((action rightHanded).tprod (action rightHanded))
abbrev Coefficient (rightHanded : Bool) := IntertwiningMap (representation rightHanded)
  (Representation.trivial ℂ WeylSpinor.Group ℂ)

def specialLinear (g : FourDoubletInvariant.Group) : WeylSpinor.Group :=
  ⟨g.val, (Matrix.mem_specialUnitaryGroup_iff.mp g.property).2⟩

theorem right_conjugate (g : WeylSpinor.Group) (v : WeylSpinor.Space) :
    WeylSpinor.right (WeylSpinor.conjugate g) v = WeylSpinor.left g v := by
  ext i
  change (∑ j, star (star ((g : Matrix (Fin 2) (Fin 2) ℂ) i j)) * v j) =
    ∑ j, (g : Matrix (Fin 2) (Fin 2) ℂ) i j * v j
  simp only [star_star]

theorem restrict_invariant (rightHanded : Bool) (f : Coefficient rightHanded) :
    FourDoubletInvariant.IsInvariant f.toLinearMap := by
  intro g a b c d
  cases rightHanded
  · exact IntertwiningMap.isIntertwining _ _ f (specialLinear g)
      ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d))
  · have h := IntertwiningMap.isIntertwining _ _ f (WeylSpinor.conjugate (specialLinear g))
      ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d))
    simp only [representation, action, ite_true, Representation.tprod_apply,
      TensorProduct.map_tmul, right_conjugate, Representation.trivial_apply] at h
    exact h

theorem eps_action (rightHanded : Bool) (g : WeylSpinor.Group) (a b : WeylSpinor.Space) :
    eps (action rightHanded g a) (action rightHanded g b) = eps a b := by
  cases rightHanded
  · exact SMEpsilonTensor.eps2_invariant _ g.property a b
  · exact SMEpsilonTensor.eps2_invariant _ (WeylSpinor.conjugate g).property a b

def pairing (rightHanded cross : Bool) : Coefficient rightHanded where
  toLinearMap := tensorPairing cross
  isIntertwining' g := by
    cases rightHanded <;> ext a b c d
    all_goals simp [representation, action, tensorPairing_apply,
      show ∀ x y, eps (WeylSpinor.left g x) (WeylSpinor.left g y) = eps x y from eps_action false g,
      show ∀ x y, eps (WeylSpinor.right g x) (WeylSpinor.right g y) = eps x y from eps_action true g]

theorem formula (rightHanded : Bool) (f : Coefficient rightHanded) :
    f = value f.toLinearMap 0 1 0 1 • pairing rightHanded false +
      value f.toLinearMap 0 0 1 1 • pairing rightHanded true := by
  apply IntertwiningMap.ext
  exact FourDoubletInvariant.formula f.toLinearMap (restrict_invariant rightHanded f)

def coordinates (rightHanded : Bool) : Coefficient rightHanded ≃ₗ[ℂ] (ℂ × ℂ) where
  toFun f := (value f.toLinearMap 0 1 0 1, value f.toLinearMap 0 0 1 1)
  invFun c := c.1 • pairing rightHanded false + c.2 • pairing rightHanded true
  left_inv f := (formula rightHanded f).symm
  right_inv c := by
    rcases c with ⟨a,b⟩
    change (value (a • tensorPairing false + b • tensorPairing true) 0 1 0 1,
      value (a • tensorPairing false + b • tensorPairing true) 0 0 1 1) = (a,b)
    simp [value, tensorPairing_apply, eps, basis]
  map_add' f h := rfl
  map_smul' z f := rfl

def basisPairing (rightHanded : Bool) : Fin 2 → Coefficient rightHanded :=
  ![pairing rightHanded false, pairing rightHanded true]
def probe : Fin 2 → FourDoubletInvariant.Tensor := ![
  (basis 0 ⊗ₜ[ℂ] basis 1) ⊗ₜ[ℂ] (basis 0 ⊗ₜ[ℂ] basis 1),
  (basis 0 ⊗ₜ[ℂ] basis 0) ⊗ₜ[ℂ] (basis 1 ⊗ₜ[ℂ] basis 1)]

theorem basisPairing_probe (rightHanded : Bool) (i j : Fin 2) :
    basisPairing rightHanded i (probe j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [basisPairing, probe, pairing, tensorPairing_apply, eps, basis]

theorem basisPairing_formula (rightHanded : Bool) (f : Coefficient rightHanded) :
    f = ∑ i, f (probe i) • basisPairing rightHanded i := by
  simpa [Fin.sum_univ_two, probe, basisPairing, value] using formula rightHanded f

variable {R X : Type*} [Group R] [AddCommMonoid X] [Module ℂ X]

/-- With an independent residual action, both local coordinates become residual Hom. -/
def flavorEquiv (rightHanded : Bool) (x : Representation ℂ R X) :
    ExternalInvariantFactorization.Coefficient (representation rightHanded) x ≃ₗ[ℂ]
      (Fin 2 → IntertwiningMap x (Representation.trivial ℂ R ℂ)) :=
  FiniteInvariantFactor.equiv (representation rightHanded) x
    (basisPairing rightHanded) probe (basisPairing_probe rightHanded)
    (basisPairing_formula rightHanded)

end
end GUT.FourSameWeylCompleteness
