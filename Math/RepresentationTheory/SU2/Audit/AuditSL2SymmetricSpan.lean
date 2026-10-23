import Math.RepresentationTheory.SU2.SL2SymmetricSpan
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Math.SL2SymmetricSpan audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.SL2SymmetricSpan.symmetricPower,
    ``Math.SL2SymmetricSpan.standard,
    ``Math.SL2SymmetricSpan.trivial,
    ``Math.SL2SymmetricSpan.of_surjective,
    ``Math.SL2SymmetricSpan.tensor,
    ``Math.SL2SymmetricSpan.tensorPower,
    ``Math.SL2SymmetricSpan.exterior,
    ``Math.SL2SymmetricSpan.coefficient_fixed_of_compact]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Math.SL2SymmetricSpan: layer and {ds.length} strict transitive checks passed"
