import Physics.StandardModel.Operators.SMLCompactWeyl
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "GUT.SMLCompactWeyl audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.SMLCompactWeyl.field_restrict,
    ``GUT.SMLCompactWeyl.field_spanned,
    ``GUT.SMLCompactWeyl.source_spanned,
    ``GUT.SMLCompactWeyl.coefficient_fixed_iff,
    ``GUT.SMLCompactWeyl.higgs_spanned,
    ``GUT.SMLCompactWeyl.higgs_coefficient_fixed_iff,
    ``GUT.SMLCompactWeyl.local_coefficient_fixed_iff,
    ``GUT.SMLCompactWeyl.coefficientEquiv,
    ``GUT.SMLCompactWeyl.compactKernelEquiv]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{d} uses unexpected axiom {ax}"
  Lean.logInfo m!"GUT.SMLCompactWeyl: layer and {ds.length} strict transitive checks passed"
