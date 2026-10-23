import Math.Audit.ImportOrigin
import Physics.FieldTheory.Jets.Higgs.Inputs.HiggsStandardInput
import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarZeroDerivativeCertificate
import Physics.FieldTheory.Jets.Weyl.Equations.PairedWeylGeneratedInput

/-! Actual physical input consumers, with no model-layer dependency. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  let owned := [`Physics.HiggsFieldDictionary, `Physics.HiggsLagrangianInput, `Physics.HiggsStandardInput,
    `Physics.ScalarConstantCoefficients, `Physics.ScalarZeroDerivativeCertificate, `Physics.PairedWeylInput]
  for ns in owned do
    let mut checked : Nat := 0
    for (d, _) in env.constants.toList do
      if ns.isPrefixOf d then
        checked := checked + 1
        for ax in (← Lean.collectAxioms d) do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
            throwError "Declaration {d} uses unexpected axiom {ax}"
    unless checked > 0 do
      throwError "Physical foundation inventory is empty: {ns}"
    Lean.logInfo m!"{ns}: {checked} strict transitive declaration checks passed"
