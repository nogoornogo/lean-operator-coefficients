import Math.RepresentationTheory.TwoComponentTensorUniqueness
import Math.RepresentationTheory.InvariantTensorCurry

/-! The symmetric triplet has an explicit nondegenerate invariant pairing,
so lower-index field strengths are equivalent to the adjoint convention. -/
namespace Math.TwoComponentTripletDual
set_option autoImplicit false
noncomputable section
open Representation TwoComponentSymmetricTensor TwoComponentTensorUniqueness Matrix
open scoped TensorProduct

def metric (x y : Triplet) : ℂ := x 0*y 2 - 2*x 1*y 1 + x 2*y 0

def bilin : Triplet →ₗ[ℂ] Triplet →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ metric
    (by intro x x' y; simp [metric]; ring)
    (by intro z x y; simp [metric]; ring)
    (by intro x y y'; simp [metric]; ring)
    (by intro z x y; simp [metric]; ring)

theorem transform (m : Matrix (Fin 2) (Fin 2) ℂ) (x y : Triplet) :
    metric ((squareMatrix m).mulVec x) ((squareMatrix m).mulVec y) =
      m.det^2 * metric x y := by
  simp [metric, squareMatrix, Matrix.mulVec, Matrix.det_fin_two,
    Matrix.vecHead, Matrix.vecTail]
  ring

def contraction : IntertwiningMap (triplet.tprod triplet) (Representation.trivial ℂ Group ℂ) where
  toLinearMap := TensorProduct.lift bilin
  isIntertwining' g := by
    apply TensorProduct.ext
    apply LinearMap.ext; intro x
    apply LinearMap.ext; intro y
    change metric ((squareMatrix (g : Matrix (Fin 2) (Fin 2) ℂ)).mulVec x)
      ((squareMatrix (g : Matrix (Fin 2) (Fin 2) ℂ)).mulVec y) = metric x y
    rw [transform, g.property]
    simp

def toDual : IntertwiningMap triplet triplet.dual :=
  InvariantTensorCurry.curry triplet triplet contraction

def fromDual : Module.Dual ℂ Triplet →ₗ[ℂ] Triplet where
  toFun phi := ![phi (basis3 2), -phi (basis3 1)/2, phi (basis3 0)]
  map_add' phi psi := by ext i; fin_cases i <;> simp; ring
  map_smul' c phi := by ext i; fin_cases i <;> simp; ring

private theorem fin_three_two (h : 2 < 3) : (⟨2,h⟩ : Fin 3) = 2 := rfl

def equiv : Representation.Equiv triplet triplet.dual where
  toLinearEquiv := {
    toLinearMap := toDual.toLinearMap
    invFun := fromDual
    left_inv x := by
      ext i
      change ![metric x (basis3 2), -metric x (basis3 1)/2, metric x (basis3 0)] i = x i
      fin_cases i
      all_goals simp only [Fin.mk_zero, Fin.mk_one, fin_three_two]
      all_goals norm_num [metric, basis3, Fin.ext_iff]
    right_inv phi := by
      apply (Pi.basisFun ℂ (Fin 3)).ext
      intro i
      simp only [Pi.basisFun_apply]
      change metric (fromDual phi) (Pi.single i 1) = phi (Pi.single i 1)
      fin_cases i
      all_goals simp only [Fin.mk_zero, Fin.mk_one, fin_three_two]
      all_goals norm_num [metric, fromDual, basis3, Fin.ext_iff]
      all_goals ring }
  isIntertwining' := toDual.isIntertwining'

end
end Math.TwoComponentTripletDual
