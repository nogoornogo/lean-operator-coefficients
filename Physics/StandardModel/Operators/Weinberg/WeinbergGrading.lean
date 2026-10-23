import Physics.StandardModel.Operators.Weinberg.WeinbergSMInterface
import Physics.StandardModel.Operators.Selection.StandardModelLocalOperator

/-! The LLHH signature and its actual coefficient scaling, not lepton-number invariance. -/
namespace Physics.WeinbergGrading
set_option autoImplicit false
noncomputable section
open SMEpsilonTensor StandardModelLocalOperator
open scoped TensorProduct

/-- Two physical left lepton doublets and two scalar Higgs doublets. -/
def quantumNumbers : QuantumNumbers where
  colorFundamentals := 2 * colorFundamentalMultiplicity .leptonDoublet
  weakFundamentals := 2 * weakFundamentalMultiplicity .leptonDoublet + 2
  leftWeyl := 2 * leftWeylMultiplicity .leptonDoublet
  rightWeyl := 2 * rightWeylMultiplicity .leptonDoublet
  sixY := 2 * sixHypercharge .leptonDoublet + 2 * 3
  threeB := 2 * threeBaryonNumber .leptonDoublet
  lepton := 2 * leptonNumber .leptonDoublet
  twiceDimension := 2 * twiceCanonicalDimension .leptonDoublet + 2 * 2

theorem signature : quantumNumbers.threeB = 0 ∧ quantumNumbers.lepton = 2 ∧
    quantumNumbers.sixY = 0 ∧ quantumNumbers.twiceDimension = 10 := by decide

variable {R F : Type*} [Group R] [AddCommGroup F] [Module ℂ F]
  (a : Representation ℂ R F)

local instance : AddCommGroup (Weak ⊗[ℂ] WeylSpinor.Space) := inferInstance
local instance : AddCommGroup (WeinbergModelSector.Lepton F) := inferInstance

theorem slot_scaling (f : WeinbergSMInterface.ModelSector a) (zL zH : ℂ)
    (l : Fin 2 → WeinbergModelSector.Lepton F) (h : Fin 2 → Weak) :
    f (exteriorPower.ιMulti ℂ 2 (fun i => zL • l i) ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ (fun i => zH • h i)) =
      (zL ^ 2 * zH ^ 2) * f (exteriorPower.ιMulti ℂ 2 l ⊗ₜ[ℂ] SymmetricPower.tprod ℂ h) := by
  rw [(exteriorPower.ιMulti ℂ 2).map_smul_univ, (SymmetricPower.tprod ℂ).map_smul_univ]
  simp only [Fin.prod_univ_two]
  rw [TensorProduct.smul_tmul_smul, map_smul]
  simp only [smul_eq_mul, pow_two]

/-- Higgs lepton charge is zero, while each lepton field has charge one. -/
theorem lepton_scaling (f : WeinbergSMInterface.ModelSector a) (z : ℂ)
    (l : Fin 2 → WeinbergModelSector.Lepton F) (h : Fin 2 → Weak) :
    f (exteriorPower.ιMulti ℂ 2 (fun i => z • l i) ⊗ₜ[ℂ] SymmetricPower.tprod ℂ h) =
      z ^ 2 * f (exteriorPower.ιMulti ℂ 2 l ⊗ₜ[ℂ] SymmetricPower.tprod ℂ h) := by
  simpa using slot_scaling a f z 1 l h

/-- On the charge circle, conjugating the coefficient reverses its weight. -/
theorem conjugate_lepton_scaling (f : WeinbergSMInterface.ModelSector a) (z : Circle)
    (l : Fin 2 → WeinbergModelSector.Lepton F) (h : Fin 2 → Weak) :
    star (f (exteriorPower.ιMulti ℂ 2 (fun i => (z : ℂ) • l i) ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ h)) =
      ((z⁻¹ : Circle) : ℂ) ^ 2 *
        star (f (exteriorPower.ιMulti ℂ 2 l ⊗ₜ[ℂ] SymmetricPower.tprod ℂ h)) := by
  rw [lepton_scaling]
  rw [star_mul, star_pow, Circle.coe_inv_eq_conj]
  exact mul_comm _ _

end
end Physics.WeinbergGrading
