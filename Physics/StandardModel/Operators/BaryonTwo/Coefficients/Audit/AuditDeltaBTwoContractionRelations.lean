import Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoContractionRelations
import Lean.Util.CollectAxioms

/-! Strict checks for the exact color/Weyl contraction relations. -/

set_option autoImplicit false

namespace Physics.DeltaBTwoContractionRelations.Audit

open SMEpsilonTensor

example (a b c d : Spin) :
    eps2 a b * eps2 c d - eps2 a c * eps2 b d + eps2 a d * eps2 b c = 0 :=
  weyl_schouten a b c d

example (u : Fin 2 → Color × Spin) (d : Fin 4 → Color × Spin) :
    blockAlternation valueO2 u d - blockAlternation valueO1 u d =
      3 * blockAlternation valueO3 u d :=
  fierz_blockAlternation u d

end Physics.DeltaBTwoContractionRelations.Audit

run_cmd do
  let declarations := [
    ``Physics.DeltaBTwoContractionRelations.weyl_schouten,
    ``Physics.DeltaBTwoContractionRelations.colorSSS_swap_first,
    ``Physics.DeltaBTwoContractionRelations.colorSSS_swap_second,
    ``Physics.DeltaBTwoContractionRelations.colorSSS_swap_third,
    ``Physics.DeltaBTwoContractionRelations.colorAAS_swap_first,
    ``Physics.DeltaBTwoContractionRelations.colorAAS_swap_second,
    ``Physics.DeltaBTwoContractionRelations.colorAAS_swap_third,
    ``Physics.DeltaBTwoContractionRelations.colorSSS_invariant,
    ``Physics.DeltaBTwoContractionRelations.colorAAS_invariant,
    ``Physics.DeltaBTwoContractionRelations.fierz_blockAlternation]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Delta-B = 2 contraction relations: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Delta-B = 2 contraction relations: {declarations.length} strict transitive axiom checks passed"
