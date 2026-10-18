import Physics.StandardModel.Operators.DevMohapatraLiteratureConvention
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Literature adapter imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.DevMohapatraLiteratureConvention.devGammaZero,
    ``GUT.DevMohapatraLiteratureConvention.devGammaTwo,
    ``GUT.DevMohapatraLiteratureConvention.devCharge,
    ``GUT.DevMohapatraLiteratureConvention.mohapatraGammaTwo,
    ``GUT.DevMohapatraLiteratureConvention.mohapatraCharge,
    ``GUT.DevMohapatraLiteratureConvention.devCharge_eq,
    ``GUT.DevMohapatraLiteratureConvention.mohapatraCharge_eq,
    ``GUT.DevMohapatraLiteratureConvention.literatureInverse,
    ``GUT.DevMohapatraLiteratureConvention.dev_inverse,
    ``GUT.DevMohapatraLiteratureConvention.mohapatra_inverse,
    ``GUT.DevMohapatraLiteratureConvention.rightComponents,
    ``GUT.DevMohapatraLiteratureConvention.rightPair,
    ``GUT.DevMohapatraLiteratureConvention.rightPair_eq,
    ``GUT.DevMohapatraLiteratureConvention.rightPair_transport,
    ``GUT.DevMohapatraLiteratureConvention.source_mass,
    ``GUT.DevMohapatraLiteratureConvention.source_vertex,
    ``GUT.DevMohapatraLiteratureConvention.downCurrent,
    ``GUT.DevMohapatraLiteratureConvention.downCurrent_transport,
    ``GUT.DevMohapatraLiteratureConvention.operator,
    ``GUT.DevMohapatraLiteratureConvention.operator_transport,
    ``GUT.DevMohapatraLiteratureConvention.coefficient,
    ``GUT.DevMohapatraLiteratureConvention.generated_literature,
    ``GUT.DevMohapatraLiteratureConvention.scalar_mass_sign,
    ``GUT.DevMohapatraLiteratureConvention.ordered_flavors,
    ``GUT.DevMohapatraLiteratureConvention.paper_comparison,
    ``GUT.DevMohapatraLiteratureConvention.ordered_paper_comparison,
    ``GUT.ChiralActionConvention.majorana_kinetic,
    ``GUT.ChiralActionConvention.flip_time,
    ``GUT.ChiralActionConvention.flip_space,
    ``GUT.ChiralActionConvention.canonical_norm_form]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Literature adapter: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Literature adapter: {ds.length} strict transitive checks passed"
