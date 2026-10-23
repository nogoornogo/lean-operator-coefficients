import Math.Audit.ImportOrigin
import Math.RepresentationTheory.Lagrangian.HiggsLagrangianInput
import Math.RepresentationTheory.Higgs.HiggsInternalSymmetry
import Math.RepresentationTheory.Jets.FiniteDerivativeScalarControl
import Math.RepresentationTheory.Jets.JetConstantProjection
import Math.Algebra.Constructions.ScalarZeroDerivative
import Math.Algebra.Constructions.PairedWeylKinetic
import Math.RepresentationTheory.Invariants.TwoSidedCovariance

/-! Namespace-wide strict transitive inventory for the reopened foundations. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  let owned := [`Math.HiggsLagrangianInput, `Math.PairedComponentFields,
    `Math.PairedJetContractions, `Math.HiggsInternalSymmetry,
    `Math.FiniteDerivativeCertificate, `Math.FiniteDerivativeScalarControl,
    `Math.JetConstantProjection, `Math.ScalarZeroDerivative,
    `Math.PairedWeylKinetic, `Math.TwoSidedCovariance, `Math.TwoSidedDifferential]
  for ns in owned do
    let mut checked : Nat := 0
    for (d, _) in env.constants.toList do
      if ns.isPrefixOf d then
        checked := checked + 1
        for ax in (← Lean.collectAxioms d) do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
            throwError "Declaration {d} uses unexpected axiom {ax}"
    unless checked > 0 do
      throwError "Foundation inventory is empty: {ns}"
    Lean.logInfo m!"{ns}: {checked} strict transitive declaration checks passed"
