import Math.RepresentationTheory.Protection.ScalarProhibitionNecessity
import Math.RepresentationTheory.Protection.ProhibitionInput
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod || (`Physics).isPrefixOf mod then
      throwError "Prohibition input imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [``Math.ScalarProhibitionNecessity.neutral_zero_control,
    ``Math.ProhibitionInput.all_mono,
    ``Math.ProhibitionInput.no_shared_iff,
    ``Math.ScalarProhibitionNecessity.forbidden_iff_detect,
    ``Math.ScalarProhibitionNecessity.not_surjective,
    ``Math.ScalarProhibitionNecessity.zero_carrier_forbidden,
    ``Math.ProhibitionInput.Forbids,
    ``Math.ProhibitionInput.AllForbids,
    ``Math.ProhibitionInput.factors_iff,
    ``Math.ProhibitionInput.factor,
    ``Math.ProhibitionInput.mono,
    ``Math.ProhibitionInput.union_iff,
    ``Math.ProhibitionInput.iUnion_iff,
    ``Math.ProhibitionInput.all_union_iff,
    ``Math.ProhibitionInput.all_iUnion_iff,
    ``Math.ProhibitionInput.empty_forbids,
    ``Math.ProhibitionInput.no_shared,
    ``Math.ProhibitionInput.shared_defeats,
    ``Math.ProhibitionInput.transport,
    ``Math.ProhibitionInput.charge_detected,
    ``Math.ProhibitionInput.restriction_obstruction]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Prohibition input: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Prohibition input: {declarations.length} strict axiom checks passed"
