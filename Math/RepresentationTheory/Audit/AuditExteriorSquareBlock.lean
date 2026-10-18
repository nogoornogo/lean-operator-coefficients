import Math.RepresentationTheory.ExteriorSquareBlock
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Math.ExteriorSquareBlock.restrict_include,
    ``Math.ExteriorSquareBlock.cut_action,
    ``Math.ExteriorSquareBlock.project_embed,
    ``Math.ExteriorSquareBlock.coreAction_eq,
    ``Math.ExteriorSquareBlock.cut_single,
    ``Math.ExteriorSquareBlock.cut_single_extra,
    ``Math.ExteriorSquareBlock.cut_single_extra_reverse]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Exterior block: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Exterior block: {declarations.length} strict axiom checks passed"
