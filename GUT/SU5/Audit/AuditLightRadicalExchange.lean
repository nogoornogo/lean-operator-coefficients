import GUT.SU5.Matching.LightRadicalExchange
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.SU5.LightRadical.onMatter_commutes,
    ``GUT.SU5.LightRadical.radical_residual,
    ``GUT.SU5.LightRadical.onLight_commutes,
    ``GUT.SU5.LightRadical.current_invariant,
    ``GUT.SU5.LightRadical.read_insert,
    ``GUT.SU5.LightRadical.read_onMatter,
    ``GUT.SU5.LightRadical.current_on_fields,
    ``GUT.SU5.LightRadical.up_current,
    ``GUT.SU5.LightRadical.electron_current,
    ``GUT.SU5.LightRadical.quark_injective,
    ``GUT.SU5.LightRadical.up_injective,
    ``GUT.SU5.LightRadical.electron_injective,
    ``GUT.SU5.LightRadicalExchange.left_invariant,
    ``GUT.SU5.LightRadicalExchange.right_invariant,
    ``GUT.SU5.LightRadicalExchange.invariant,
    ``GUT.SU5.LightRadicalExchange.left_on_fields,
    ``GUT.SU5.LightRadicalExchange.right_on_fields,
    ``GUT.SU5.LightRadicalExchange.coefficient_on_fields,
    ``GUT.SU5.LightRadicalExchange.exterior_on_fields,
    ``GUT.SU5.LightRadicalExchange.generated_nonzero,
    ``GUT.SU5.LightRadicalExchange.one_generation,
    ``GUT.SU5.LightRadicalExchange.three_generations]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Light radical exchange: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Light radical exchange: {declarations.length} strict axiom checks passed"
