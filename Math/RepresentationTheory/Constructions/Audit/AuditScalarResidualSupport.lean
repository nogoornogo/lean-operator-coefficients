import Math.RepresentationTheory.Constructions.ScalarResidualSupport
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Scalar residual support imports application {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.ScalarResidualSupport.restrict,
    ``Math.ScalarResidualSupport.neutral_of_allowed,
    ``Math.ScalarResidualSupport.extend,
    ``Math.ScalarResidualSupport.equiv,
    ``Math.ScalarResidualSupport.allowed_iff,
    ``Math.ScalarResidualSupport.exists_guard_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Scalar residual support: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Scalar residual support: layer and {ds.length} strict transitive axiom checks passed"
