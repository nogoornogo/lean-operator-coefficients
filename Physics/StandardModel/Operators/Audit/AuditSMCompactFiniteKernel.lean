import Physics.StandardModel.Operators.SMQLFullKernel
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "SM compact finite kernel imports GUT application {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.SMColorIntegralBasis.color_basis_eigen,
    ``GUT.SMColorIntegralBasis.gauge_basis_eigen,
    ``GUT.SMColorIntegralBasis.field_basis_eigen,
    ``GUT.SMColorIntegralBasis.raw_basis_eigen,
    ``GUT.SMColorIntegralBasis.raw_integral,
    ``GUT.SMColorIntegralBasis.source_integral,
    ``GUT.SMIntegralLocalWeights.source_color,
    ``GUT.SMIntegralLocalWeights.source_weak,
    ``GUT.SMIntegralLocalWeights.source_hyper,
    ``GUT.SMIntegralLocalWeights.boson_color,
    ``GUT.SMIntegralLocalWeights.boson_weak,
    ``GUT.SMIntegralLocalWeights.boson_hyper,
    ``GUT.SMIntegralLocalWeights.action_color,
    ``GUT.SMIntegralLocalWeights.action_weak,
    ``GUT.SMIntegralLocalWeights.action_hyper,
    ``GUT.SMFullLocalKernel.card_tests,
    ``GUT.SMFullLocalKernel.exhaustive,
    ``GUT.SMFullLocalKernel.coefficientEquiv,
    ``GUT.SMFullLocalKernel.allowed_iff_rank_lt,
    ``GUT.SMQLFullKernel.coefficientEquiv,
    ``GUT.SMQLFullKernel.local_allowed_iff,
    ``GUT.SMQLFullKernel.original_allowed_iff,
    ``GUT.SMQLFullKernel.test_allowed_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SM compact finite kernel: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"SM compact finite kernel: layer and {ds.length} strict transitive axiom checks passed"
