import Math.Audit.ImportOrigin
import GUT.Spin10.SelectionRules.StandardChain

open Physics

open Math

/-! The actual Spin inclusion specializes the shared SU(5) theorem.
These tests retain the light target as a model input, not a half-spin inhabitant. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU6).isPrefixOf mod || (`GUT.Sp).isPrefixOf mod then
      throwError "Compact Spin standard chain imports an unrelated gauge family: {mod}"

namespace GUT.CompactSpin.AuditStandardChain

open Math.CompactSpin
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

example {rho : Representation ℂ (Group 10 × Multiplicative (ZMod 3)) E}
    (M : StandardChain.Model rho) :
    ¬ StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator M.lightSpectrum :=
  StandardChain.selection_rule_obstruction M

example {rho : Representation ℂ (Group 10 × Circle) E}
    (M : StandardChain.Model rho)
    (hc : Continuous (fun p : (Group 10 × Circle) × E => rho p.1 p.2)) :
    (StandardChain.continuousModel M hc).toModel = M := rfl

example {rho : Representation ℂ (Group 10 × Circle) E}
    (M : StandardChain.Model rho)
    (hc : Continuous (fun p : (Group 10 × Circle) × E => rho p.1 p.2)) :
    Continuous (fun p : (SU5 × Circle) × E =>
      GUT.StandardChain.pullback SU5Inclusion rho p.1 p.2) :=
  (StandardChain.continuousModel M hc).pullback_continuous

#print axioms StandardChain.selection_rule_obstruction
#print axioms StandardChain.continuousModel
#print axioms StandardChain.continuous_selection_rule_obstruction
#print axioms StandardChain.scalar_selection_rule_obstruction
#print axioms StandardChain.scalarContinuousModel
#print axioms GUT.StandardChain.Model.actual_signature_pair

end

end GUT.CompactSpin.AuditStandardChain
