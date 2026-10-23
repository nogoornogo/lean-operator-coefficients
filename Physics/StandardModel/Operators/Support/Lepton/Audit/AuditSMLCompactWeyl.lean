import Physics.StandardModel.Operators.Support.Lepton.SMLCompactWeyl
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "GUT.SMLCompactWeyl audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.SMLCompactWeyl.field_restrict,
    ``Physics.SMLCompactWeyl.field_spanned,
    ``Physics.SMLCompactWeyl.source_spanned,
    ``Physics.SMLCompactWeyl.coefficient_fixed_iff,
    ``Physics.SMLCompactWeyl.higgs_spanned,
    ``Physics.SMLCompactWeyl.higgs_coefficient_fixed_iff,
    ``Physics.SMLCompactWeyl.local_coefficient_fixed_iff,
    ``Physics.SMLCompactWeyl.coefficientEquiv,
    ``Physics.SMLCompactWeyl.compactKernelEquiv]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Physics.SMLCompactWeyl: layer and {ds.length} strict transitive checks passed"
