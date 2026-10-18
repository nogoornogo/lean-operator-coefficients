import Physics.StandardModel.Spectrum.ExactSMWeightMultiplicity

open Math

/-! Nonzero gauge eigenvectors at the four monitored qque weights. -/

namespace GUT.MonitoredSMWeights
noncomputable section
open scoped TensorProduct
open Representation StandardSMGaugeTensor SMEpsilonTensor
open SU5 SU5.TorusCharacter StandardSMCharacterTarget

theorem quark_vector_nonzero (a : Fin 3) (b : Fin 2) :
    colorBasis a ⊗ₜ[ℂ] weakBasis b ≠ 0 := by
  simpa [colorBasis, weakBasis] using
    ((Pi.basisFun ℂ (Fin 3)).tensorProduct (Pi.basisFun ℂ (Fin 2))).ne_zero (a, b)

theorem up_vector_nonzero : (LinearMap.proj (2 : Fin 3) : Module.Dual ℂ Color) ≠ 0 := by
  intro h
  have he := LinearMap.congr_fun h (colorBasis 2)
  simp [colorBasis] at he

theorem electron_vector_nonzero : (LinearMap.id : Module.Dual ℂ ℂ) ≠ 0 := by
  intro h
  have he := LinearMap.congr_fun h 1
  simp at he

theorem color_vector (z : PhysicalTorus.Coordinates) (a : Fin 3) :
    color (PhysicalTorus.gaugePoint z) (colorBasis a) =
      ((![z 0, z 1, (z 0 * z 1)⁻¹] a : Circle) : ℂ) • colorBasis a := by
  ext b
  fin_cases a <;> fin_cases b <;>
    simp [color, colorBasis, PhysicalTorus.gaugePoint, PhysicalTorus.color,
      MaximalTorus.diagonalElement, Matrix.toLin'_apply]

theorem weak_vector (z : PhysicalTorus.Coordinates) (a : Fin 2) :
    weak (PhysicalTorus.gaugePoint z) (weakBasis a) =
      ((![z 2, (z 2)⁻¹] a : Circle) : ℂ) • weakBasis a := by
  ext b
  fin_cases a <;> fin_cases b <;>
    simp [weak, weakBasis, PhysicalTorus.gaugePoint, PhysicalTorus.weak,
      MaximalTorus.diagonalElement, Matrix.toLin'_apply]

theorem quark_zero (z : PhysicalTorus.Coordinates) :
    quark (PhysicalTorus.gaugePoint z) (colorBasis 0 ⊗ₜ[ℂ] weakBasis 0) =
      (weightCharacter (smReducedWeight 0) (PhysicalTorus.toTorus z) : ℂ) •
        (colorBasis 0 ⊗ₜ[ℂ] weakBasis 0) := by
  simp only [quark, twist, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply,
    Representation.tprod_apply, TensorProduct.map_tmul, color_vector, weak_vector,
    TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
  congr 1
  norm_num [PhysicalTorus.weightCharacter_toTorus, PhysicalTorus.exponent,
    Fin.prod_univ_succ, smReducedWeight, phase, PhysicalTorus.gaugePoint]
  congr 1
  ring

theorem quark_three (z : PhysicalTorus.Coordinates) :
    quark (PhysicalTorus.gaugePoint z) (colorBasis 1 ⊗ₜ[ℂ] weakBasis 1) =
      (weightCharacter (smReducedWeight 3) (PhysicalTorus.toTorus z) : ℂ) •
        (colorBasis 1 ⊗ₜ[ℂ] weakBasis 1) := by
  simp only [quark, twist, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply,
    Representation.tprod_apply, TensorProduct.map_tmul, color_vector, weak_vector,
    TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
  congr 1
  norm_num [PhysicalTorus.weightCharacter_toTorus, PhysicalTorus.exponent,
    Fin.prod_univ_succ, smReducedWeight, phase, PhysicalTorus.gaugePoint]
  congr 1
  ring

theorem up_eight (z : PhysicalTorus.Coordinates) :
    upRight.dual (PhysicalTorus.gaugePoint z) (LinearMap.proj (2 : Fin 3)) =
      (weightCharacter (smReducedWeight 8) (PhysicalTorus.toTorus z) : ℂ) •
        (LinearMap.proj (2 : Fin 3) : Module.Dual ℂ Color) := by
  apply LinearMap.ext
  intro x
  have hc : (color (PhysicalTorus.gaugePoint z)⁻¹ x) 2 =
      (z 0 : ℂ) * (z 1 : ℂ) * x 2 := by
    change (star (Matrix.diagonal (fun i =>
      (![z 0, z 1, (z 0 * z 1)⁻¹] i : ℂ)))).mulVec x 2 = _
    simp [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mulVec_diagonal,
      ← Circle.coe_inv_eq_conj, mul_comm]
  change phase 4 (PhysicalTorus.gaugePoint z)⁻¹ * (color (PhysicalTorus.gaugePoint z)⁻¹ x) 2 = _
  rw [hc]
  simp [phase, PhysicalTorus.gaugePoint,
    PhysicalTorus.weightCharacter_toTorus, PhysicalTorus.exponent,
    Fin.prod_univ_succ, smReducedWeight]
  ring

theorem electron_fourteen (z : PhysicalTorus.Coordinates) :
    electronRight.dual (PhysicalTorus.gaugePoint z) (LinearMap.id : Module.Dual ℂ ℂ) =
      (weightCharacter (smReducedWeight 14) (PhysicalTorus.toTorus z) : ℂ) •
        (LinearMap.id : Module.Dual ℂ ℂ) := by
  apply LinearMap.ext
  intro x
  change electronRight (PhysicalTorus.gaugePoint z)⁻¹ x = _
  simp [electronRight, twist, phase, PhysicalTorus.gaugePoint, Representation.trivial,
    PhysicalTorus.weightCharacter_toTorus, PhysicalTorus.exponent,
    Fin.prod_univ_succ, smReducedWeight]

end
end GUT.MonitoredSMWeights
