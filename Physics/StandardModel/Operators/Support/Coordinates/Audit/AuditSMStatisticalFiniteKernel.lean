import Physics.StandardModel.Operators.Support.Quark.SMQLPartialKernel
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "SM statistical finite kernel imports GUT application {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.WeylRealTransvections.card_index,
    ``Physics.WeylRealTransvections.split_transvection,
    ``Physics.WeylRealTransvections.generates,
    ``Physics.WeylRealTransvections.spinor_affine,
    ``Physics.WeylRealTransvections.card_tests,
    ``Physics.WeylRealTransvections.exhaustive,
    ``Physics.SMWeylFiniteKernel.fieldDirection,
    ``Physics.SMWeylFiniteKernel.field_affine,
    ``Physics.SMWeylFiniteKernel.source_polynomial,
    ``Physics.SMWeylFiniteKernel.boson_fixed,
    ``Physics.SMWeylFiniteKernel.action_polynomial,
    ``Physics.SMWeylFiniteKernel.exhaustive,
    ``Physics.SMWeylFiniteKernel.coefficientEquiv,
    ``Physics.SMWeylFiniteKernel.allowed_iff_rank_lt,
    ``Physics.SMWeylFiniteKernel.basis,
    ``Physics.SMWeylFiniteKernel.canonicalEquiv,
    ``Physics.SMQLPartialKernel.coefficientEquiv,
    ``Physics.SMQLPartialKernel.local_allowed_iff,
    ``Physics.SMQLPartialKernel.original_allowed_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SM statistical finite kernel: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"SM statistical finite kernel: layer and {ds.length} strict transitive axiom checks passed"
