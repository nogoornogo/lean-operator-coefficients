import Math.Audit.ImportOrigin
import Math.LinearAlgebra.PolarizedExteriorAction
import Mathlib.Tactic.NormNum

/-! The covector must transform by the inverse map. A non-involutive
dilation detects accidentally using the forward map instead. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf mod || (`GUT.SU6).isPrefixOf mod ||
        (`GUT.SUN).isPrefixOf mod || (`GUT.Spin).isPrefixOf mod || (`GUT.Sp).isPrefixOf mod then
      throwError "Exterior naturality imports a gauge family: {mod}"

namespace Math.ExteriorNaturality.Audit

noncomputable section

def dilation : ℚ ≃ₗ[ℚ] ℚ := LinearEquiv.smulOfNeZero ℚ ℚ 2 (by norm_num)

theorem inverse_covector_control :
    ((LinearMap.id : Module.Dual ℚ ℚ).comp dilation.symm.toLinearMap) (dilation 1) = 1 := by
  simp

theorem forward_covector_wrong :
    ((LinearMap.id : Module.Dual ℚ ℚ).comp dilation.toLinearMap) (dilation 1) ≠ 1 := by
  norm_num [dilation, LinearEquiv.smulOfNeZero_apply]

example (s : ExteriorAlgebra ℚ ℚ) :
    mapEquiv dilation (CliffordAlgebra.contractLeft LinearMap.id s) =
      CliffordAlgebra.contractLeft
        ((LinearMap.id : Module.Dual ℚ ℚ).comp dilation.symm.toLinearMap)
        (mapEquiv dilation s) := mapEquiv_contract dilation LinearMap.id s

#print axioms map_contract
#print axioms mapEquiv
#print axioms mapEquiv_contract
#print axioms mapEquiv_creation
#print axioms PolarizedExteriorAction.dualAction_pairing
#print axioms PolarizedExteriorAction.cliffordOperator_naturality
#print axioms inverse_covector_control
#print axioms forward_covector_wrong

end

end Math.ExteriorNaturality.Audit
