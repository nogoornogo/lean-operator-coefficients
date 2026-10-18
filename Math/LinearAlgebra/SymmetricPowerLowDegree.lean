import TauCeti.LinearAlgebra.SymmetricPower.Lift
import Mathlib.Basic.Complex.Basic
import TauCeti.RepresentationTheory.SymmetricPower

/-! Explicit degree-one symmetric-power transport, without basis choices. -/
namespace Math.SymmetricPowerLowDegree
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
variable {B : Type*} [AddCommGroup B] [Module ℂ B]

def zeroEvaluation : Sym[ℂ]^0 B →ₗ[ℂ] ℂ :=
  SymmetricPower.lift
    (MultilinearMap.constOfIsEmpty ℂ (fun _ : Fin 0 => B) (1 : ℂ)) (by
      intro e
      ext w
      rfl)

def zeroInclusion : ℂ →ₗ[ℂ] Sym[ℂ]^0 B :=
  (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight
    (SymmetricPower.tprod ℂ (fun i : Fin 0 => Fin.elim0 i))

@[simp] theorem zeroEvaluation_tprod (w : Fin 0 → B) :
    zeroEvaluation (SymmetricPower.tprod ℂ w) = 1 := by
  simp [zeroEvaluation, MultilinearMap.constOfIsEmpty]

def zeroEquiv : Sym[ℂ]^0 B ≃ₗ[ℂ] ℂ where
  toLinearMap := zeroEvaluation
  invFun := zeroInclusion
  left_inv := by
    have h : zeroInclusion.comp zeroEvaluation = (LinearMap.id : Sym[ℂ]^0 B →ₗ[ℂ] _) := by
      apply SymmetricPower.ext
      intro w
      simp only [LinearMap.comp_apply, zeroEvaluation_tprod, zeroInclusion,
        LinearMap.smulRight_apply, LinearMap.id_apply, one_smul]
      congr 1
      funext i
      exact Fin.elim0 i
    exact LinearMap.congr_fun h
  right_inv := by
    intro z
    change zeroEvaluation (z • SymmetricPower.tprod ℂ (fun i : Fin 0 => Fin.elim0 i)) = z
    rw [map_smul, zeroEvaluation_tprod, smul_eq_mul, mul_one]

def representationZeroEquiv {G : Type*} [Group G] (r : Representation ℂ G B) :
    Representation.Equiv (r.symmetricPower 0) (Representation.trivial ℂ G ℂ) where
  toLinearEquiv := zeroEquiv
  isIntertwining' g := by
    apply SymmetricPower.ext
    intro w
    change zeroEvaluation (r.symmetricPower 0 g (SymmetricPower.tprod ℂ w)) =
      zeroEvaluation (SymmetricPower.tprod ℂ w)
    rw [Representation.symmetricPower_apply_tprod, zeroEvaluation_tprod, zeroEvaluation_tprod]

def inclusion : B →ₗ[ℂ] Sym[ℂ]^1 B :=
  (MultilinearMap.ofSubsingleton (R := ℂ) (M₂ := B) (M₃ := Sym[ℂ]^1 B)
    (0 : Fin 1)).symm (SymmetricPower.tprod ℂ)

def evaluation : Sym[ℂ]^1 B →ₗ[ℂ] B :=
  SymmetricPower.lift
    (MultilinearMap.ofSubsingleton (R := ℂ) (M₂ := B) (M₃ := B)
      (0 : Fin 1) LinearMap.id) (by
        intro e
        have he : e = Equiv.refl (Fin 1) := Subsingleton.elim _ _
        subst e
        ext w
        rfl)

@[simp] theorem inclusion_apply (b : B) :
    inclusion b = SymmetricPower.tprod ℂ (fun _ : Fin 1 => b) := rfl

@[simp] theorem evaluation_tprod (w : Fin 1 → B) :
    evaluation (SymmetricPower.tprod ℂ w) = w 0 := by
  simp [evaluation, MultilinearMap.ofSubsingleton]

def oneEquiv : Sym[ℂ]^1 B ≃ₗ[ℂ] B where
  toLinearMap := evaluation
  invFun := inclusion
  left_inv := by
    have h : inclusion.comp evaluation = (LinearMap.id : Sym[ℂ]^1 B →ₗ[ℂ] _) := by
      apply SymmetricPower.ext
      intro w
      simp only [LinearMap.comp_apply, evaluation_tprod, inclusion_apply, LinearMap.id_apply]
      congr 1
      funext i
      exact congrArg w (Subsingleton.elim 0 i)
    exact LinearMap.congr_fun h
  right_inv := by intro b; simp

def representationOneEquiv {G : Type*} [Group G] (r : Representation ℂ G B) :
    Representation.Equiv (r.symmetricPower 1) r where
  toLinearEquiv := oneEquiv
  isIntertwining' g := by
    apply SymmetricPower.ext
    intro w
    change evaluation (r.symmetricPower 1 g (SymmetricPower.tprod ℂ w)) =
      r g (evaluation (SymmetricPower.tprod ℂ w))
    rw [Representation.symmetricPower_apply_tprod, evaluation_tprod, evaluation_tprod]

end
end Math.SymmetricPowerLowDegree
