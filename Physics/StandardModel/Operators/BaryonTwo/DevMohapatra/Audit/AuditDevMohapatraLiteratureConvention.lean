import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraLiteratureConvention
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Literature adapter imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.DevMohapatraLiteratureConvention.devGammaZero,
    ``Physics.DevMohapatraLiteratureConvention.devGammaTwo,
    ``Physics.DevMohapatraLiteratureConvention.devCharge,
    ``Physics.DevMohapatraLiteratureConvention.mohapatraGammaTwo,
    ``Physics.DevMohapatraLiteratureConvention.mohapatraCharge,
    ``Physics.DevMohapatraLiteratureConvention.devCharge_eq,
    ``Physics.DevMohapatraLiteratureConvention.mohapatraCharge_eq,
    ``Physics.DevMohapatraLiteratureConvention.literatureInverse,
    ``Physics.DevMohapatraLiteratureConvention.dev_inverse,
    ``Physics.DevMohapatraLiteratureConvention.mohapatra_inverse,
    ``Physics.DevMohapatraLiteratureConvention.rightComponents,
    ``Physics.DevMohapatraLiteratureConvention.rightPair,
    ``Physics.DevMohapatraLiteratureConvention.rightPair_eq,
    ``Physics.DevMohapatraLiteratureConvention.rightPair_transport,
    ``Physics.DevMohapatraLiteratureConvention.source_mass,
    ``Physics.DevMohapatraLiteratureConvention.source_vertex,
    ``Physics.DevMohapatraLiteratureConvention.downCurrent,
    ``Physics.DevMohapatraLiteratureConvention.downCurrent_transport,
    ``Physics.DevMohapatraLiteratureConvention.operator,
    ``Physics.DevMohapatraLiteratureConvention.operator_transport,
    ``Physics.DevMohapatraLiteratureConvention.coefficient,
    ``Physics.DevMohapatraLiteratureConvention.generated_literature,
    ``Physics.DevMohapatraLiteratureConvention.scalar_mass_sign,
    ``Physics.DevMohapatraLiteratureConvention.ordered_flavors,
    ``Physics.DevMohapatraLiteratureConvention.paper_comparison,
    ``Physics.DevMohapatraLiteratureConvention.ordered_paper_comparison,
    ``Physics.ChiralActionConvention.majorana_kinetic,
    ``Physics.ChiralActionConvention.flip_time,
    ``Physics.ChiralActionConvention.flip_space,
    ``Physics.ChiralActionConvention.canonical_norm_form]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Literature adapter: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Literature adapter: {ds.length} strict transitive checks passed"
