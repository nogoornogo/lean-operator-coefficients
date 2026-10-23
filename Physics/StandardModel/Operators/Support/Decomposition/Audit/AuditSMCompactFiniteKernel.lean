import Physics.StandardModel.Operators.Support.Quark.SMQLFullKernel
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "SM compact finite kernel imports GUT application {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.SMColorIntegralBasis.color_basis_eigen,
    ``Physics.SMColorIntegralBasis.gauge_basis_eigen,
    ``Physics.SMColorIntegralBasis.field_basis_eigen,
    ``Physics.SMColorIntegralBasis.raw_basis_eigen,
    ``Physics.SMColorIntegralBasis.raw_integral,
    ``Physics.SMColorIntegralBasis.source_integral,
    ``Physics.SMIntegralLocalWeights.source_color,
    ``Physics.SMIntegralLocalWeights.source_weak,
    ``Physics.SMIntegralLocalWeights.source_hyper,
    ``Physics.SMIntegralLocalWeights.boson_color,
    ``Physics.SMIntegralLocalWeights.boson_weak,
    ``Physics.SMIntegralLocalWeights.boson_hyper,
    ``Physics.SMIntegralLocalWeights.action_color,
    ``Physics.SMIntegralLocalWeights.action_weak,
    ``Physics.SMIntegralLocalWeights.action_hyper,
    ``Physics.SMFullLocalKernel.card_tests,
    ``Physics.SMFullLocalKernel.exhaustive,
    ``Physics.SMFullLocalKernel.coefficientEquiv,
    ``Physics.SMFullLocalKernel.allowed_iff_rank_lt,
    ``Physics.SMQLFullKernel.coefficientEquiv,
    ``Physics.SMQLFullKernel.local_allowed_iff,
    ``Physics.SMQLFullKernel.original_allowed_iff,
    ``Physics.SMQLFullKernel.test_allowed_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SM compact finite kernel: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"SM compact finite kernel: layer and {ds.length} strict transitive axiom checks passed"
