import Physics.StandardModel.Operators.SixQuarkConventionalBasis
import Physics.StandardModel.Operators.SixQuarkConventionalCoordinates
import Physics.StandardModel.Operators.SixQuarkGrassmannNormalization
import Physics.FieldTheory.Spinor.RightWeylChargeConjugation
import Lean.Util.CollectAxioms

/-! Strict transitive checks of conventional coordinates and normalization. -/
run_cmd do
  let declarations := [
    ``GUT.SixQuarkConventionalBasis.colorSSS_invariant,
    ``GUT.SixQuarkConventionalBasis.colorAAS_invariant,
    ``GUT.SixQuarkConventionalBasis.combine_invariant,
    ``GUT.SixQuarkConventionalBasis.orderedO1_apply,
    ``GUT.SixQuarkConventionalBasis.orderedO2_apply,
    ``GUT.SixQuarkConventionalBasis.orderedO3_apply,
    ``GUT.SixQuarkConventionalBasis.orderedO1_invariant,
    ``GUT.SixQuarkConventionalBasis.orderedO2_invariant,
    ``GUT.SixQuarkConventionalBasis.orderedO3_invariant,
    ``GUT.SixQuarkConventionalBasis.descend,
    ``GUT.SixQuarkConventionalBasis.orderedO3_eq_existing,
    ``GUT.SixQuarkConventionalBasis.O3_eq_existing,
    ``GUT.SixQuarkConventionalBasis.O3_witness,
    ``GUT.RightWeylChargeConjugation.charge_eq,
    ``GUT.RightWeylChargeConjugation.gamma_hermitian,
    ``GUT.RightWeylChargeConjugation.gamma_clifford,
    ``GUT.RightWeylChargeConjugation.chirality_orientation,
    ``GUT.RightWeylChargeConjugation.charge_gamma,
    ``GUT.RightWeylChargeConjugation.charge_transpose,
    ``GUT.RightWeylChargeConjugation.charge_conjTranspose,
    ``GUT.RightWeylChargeConjugation.projector_eq,
    ``GUT.RightWeylChargeConjugation.projector_idempotent,
    ``GUT.RightWeylChargeConjugation.projector_embedRight,
    ``GUT.RightWeylChargeConjugation.right_diquark,
    ``GUT.RightWeylChargeConjugation.three_right_diquarks,
    ``GUT.DeltaBTwoContractionRelations.blockAlternation_eq,
    ``GUT.SixQuarkConventionalCoordinates.descend_block,
    ``GUT.SixQuarkConventionalCoordinates.O1_block,
    ``GUT.SixQuarkConventionalCoordinates.O2_block,
    ``GUT.SixQuarkConventionalCoordinates.O3_block,
    ``GUT.SixQuarkConventionalCoordinates.probes_O1,
    ``GUT.SixQuarkConventionalCoordinates.probes_O2,
    ``GUT.SixQuarkConventionalCoordinates.probes_O3,
    ``GUT.SixQuarkConventionalCoordinates.conventional_determinant,
    ``GUT.SixQuarkConventionalCoordinates.fierz,
    ``GUT.SixQuarkConventionalCoordinates.conventionalEquiv,
    ``GUT.SixQuarkConventionalCoordinates.reconstruct,
    ``GUT.SixQuarkConventionalCoordinates.probes_Q1,
    ``GUT.SixQuarkConventionalCoordinates.probes_Q4,
    ``GUT.SixQuarkConventionalCoordinates.chiralEquiv,
    ``GUT.SixQuarkConventionalCoordinates.reconstruct_chiral,
    ``GUT.SixQuarkGrassmannNormalization.pairing_ordered,
    ``GUT.SixQuarkGrassmannNormalization.ordered_eq_sector,
    ``GUT.SixQuarkGrassmannNormalization.basis_independent,
    ``GUT.SixQuarkGrassmannNormalization.O1_fourComponent,
    ``GUT.SixQuarkGrassmannNormalization.O2_fourComponent,
    ``GUT.SixQuarkGrassmannNormalization.O3_fourComponent,
    ``GUT.SixQuarkGrassmannNormalization.grassmann_reconstruct,
    ``GUT.SixQuarkGrassmannNormalization.grassmann_reconstruct_chiral,
    ``GUT.SixQuarkGrassmannNormalization.ordered_monomial,
    ``GUT.SixQuarkGrassmannNormalization.species_factorial,
    ``GUT.SixQuarkGrassmannNormalization.normalized_polynomial,
    ``GUT.SixQuarkGrassmannNormalization.species_block_sign]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Conventional six-quark checkpoint: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Conventional six-quark checkpoint: {declarations.length} strict transitive checks passed"
