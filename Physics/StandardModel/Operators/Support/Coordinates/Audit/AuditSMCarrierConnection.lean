import Math.Audit.ImportOrigin
import Physics.StandardModel.Operators.Support.Lepton.SMLowerGenerationSupport
import Physics.StandardModel.Operators.Support.Quark.SMQ18LocalSupport

/-! Strict actual-source return audit for the Q18 carrier and local consumers. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "SM carrier imports forbidden layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Physics.SMQ18Support.actualFieldEquiv,
    ``Physics.SMQ18Support.actualQuarkEquiv,
    ``Physics.SMQ18Support.PresentedField.linearEquiv,
    ``Physics.SMQ18Support.PresentedField.action,
    ``Physics.SMQ18Support.PresentedField.representationEquiv,
    ``Physics.SMQ18Support.PresentedField.dimension,
    ``Physics.SMQ18Support.PresentedField.determinant,
    ``Physics.SMQ18Support.PresentedField.middleDuality,
    ``Physics.SMQ18Support.semisimple_allowed,
    ``Physics.SMGenerationCoefficients.local_of_coefficient,
    ``Physics.SMGenerationCoefficients.local_of_presented_generation,
    ``Physics.SMGenerationCoefficients.local_of_presented_generation_at,
    ``Physics.SMLowerGenerationSupport.quark_local,
    ``Physics.SMLowerGenerationSupport.quark_kernel,
    ``Physics.SMQ18LocalSupport.restricted_of_coefficient,
    ``Physics.SMQ18LocalSupport.restricted_of_presented_generation,
    ``Physics.SMQ18LocalSupport.kernel_of_compact,
    ``Physics.SMQ18LocalSupport.restricted_allowed,
    ``Physics.SMQ18LocalSupport.kernel_allowed,
    ``Physics.SMQ18LocalSupport.local_allowed]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SM carrier connection {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Q18 carrier and local connection: {ds.length} strict transitive checks passed"
