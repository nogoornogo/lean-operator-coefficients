import Math.RepresentationTheory.Content.FiniteFlavorControls
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

/-! Both finite groups, dimensions, and positive/negative controls are kernel checked. -/

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Flavor controls import application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.FiniteFlavorControls.s3,
    ``Math.FiniteFlavorControls.a4,
    ``Math.FiniteFlavorControls.standard_preserves_hermitian,
    ``Math.FiniteFlavorControls.s3_dimension,
    ``Math.FiniteFlavorControls.a4_dimension,
    ``Math.FiniteFlavorControls.s3_noncommuting,
    ``Math.FiniteFlavorControls.a4_noncommuting,
    ``Math.FiniteFlavorControls.s3_no_invariant_functional,
    ``Math.FiniteFlavorControls.a4_no_invariant_functional,
    ``Math.FiniteFlavorControls.s3_pairedCoefficient_ne_zero,
    ``Math.FiniteFlavorControls.a4_pairedCoefficient_ne_zero,
    ``Math.FiniteFlavorControls.s3_unmatched_four_no_invariant,
    ``Math.FiniteFlavorControls.a4_unmatched_four_no_invariant]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Flavor controls: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Flavor controls: layer and {declarations.length} strict axiom checks passed"
