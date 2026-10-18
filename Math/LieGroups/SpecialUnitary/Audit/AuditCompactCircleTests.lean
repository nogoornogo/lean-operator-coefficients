import Math.LieGroups.SpecialUnitary.ColorPlaneCircles
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Compact circle tests import application {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.IntegralTorusTests.sample_powers,
    ``Math.IntegralTorusTests.sample_ne_one,
    ``Math.IntegralTorusTests.of_bounded,
    ``Math.IntegralTorusTests.of_basis,
    ``Math.IntegralTorusTests.invariant,
    ``Math.IntegralTorusTests.conjugate_invariant,
    ``Math.IntegralTorusTests.of_surjective,
    ``Math.IntegralTorusTests.tensor,
    ``Math.IntegralTorusTests.scalar,
    ``Math.TwoCircleGeneration.mix,
    ``Math.TwoCircleGeneration.rotation_conjugate,
    ``Math.TwoCircleGeneration.first_row_ext,
    ``Math.TwoCircleGeneration.euler,
    ``Math.TwoCircleGeneration.invariant,
    ``Math.TwoCircleGeneration.exhaustive,
    ``Math.ColorPlaneCircles.embedding_matrix,
    ``Math.ColorPlaneCircles.form,
    ``Math.ColorPlaneCircles.rotation01_eq,
    ``Math.ColorPlaneCircles.rotation02_eq,
    ``Math.ColorPlaneCircles.tail_eq,
    ``Math.ColorPlaneCircles.invariant,
    ``Math.ColorPlaneCircles.embedding_conjugate,
    ``Math.ColorPlaneCircles.embedding_mix,
    ``Math.ColorPlaneCircles.exhaustive]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Compact circle tests: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Compact circle tests: layer and {ds.length} strict transitive axiom checks passed"
