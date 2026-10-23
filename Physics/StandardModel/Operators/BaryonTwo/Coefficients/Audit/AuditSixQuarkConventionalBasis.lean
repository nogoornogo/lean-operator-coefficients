import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkConventionalBasis
import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkConventionalCoordinates
import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkGrassmannNormalization
import Physics.FieldTheory.Spinor.Weyl.RightWeylChargeConjugation
import Lean.Util.CollectAxioms

/-! Strict transitive checks of conventional coordinates and normalization. -/
run_cmd do
  let declarations := [
    ``Physics.SixQuarkConventionalBasis.colorSSS_invariant,
    ``Physics.SixQuarkConventionalBasis.colorAAS_invariant,
    ``Physics.SixQuarkConventionalBasis.combine_invariant,
    ``Physics.SixQuarkConventionalBasis.orderedO1_apply,
    ``Physics.SixQuarkConventionalBasis.orderedO2_apply,
    ``Physics.SixQuarkConventionalBasis.orderedO3_apply,
    ``Physics.SixQuarkConventionalBasis.orderedO1_invariant,
    ``Physics.SixQuarkConventionalBasis.orderedO2_invariant,
    ``Physics.SixQuarkConventionalBasis.orderedO3_invariant,
    ``Physics.SixQuarkConventionalBasis.descend,
    ``Physics.SixQuarkConventionalBasis.orderedO3_eq_existing,
    ``Physics.SixQuarkConventionalBasis.O3_eq_existing,
    ``Physics.SixQuarkConventionalBasis.O3_witness,
    ``Physics.RightWeylChargeConjugation.charge_eq,
    ``Physics.RightWeylChargeConjugation.gamma_hermitian,
    ``Physics.RightWeylChargeConjugation.gamma_clifford,
    ``Physics.RightWeylChargeConjugation.chirality_orientation,
    ``Physics.RightWeylChargeConjugation.charge_gamma,
    ``Physics.RightWeylChargeConjugation.charge_transpose,
    ``Physics.RightWeylChargeConjugation.charge_conjTranspose,
    ``Physics.RightWeylChargeConjugation.projector_eq,
    ``Physics.RightWeylChargeConjugation.projector_idempotent,
    ``Physics.RightWeylChargeConjugation.projector_embedRight,
    ``Physics.RightWeylChargeConjugation.right_diquark,
    ``Physics.RightWeylChargeConjugation.three_right_diquarks,
    ``Physics.DeltaBTwoContractionRelations.blockAlternation_eq,
    ``Physics.SixQuarkConventionalCoordinates.descend_block,
    ``Physics.SixQuarkConventionalCoordinates.O1_block,
    ``Physics.SixQuarkConventionalCoordinates.O2_block,
    ``Physics.SixQuarkConventionalCoordinates.O3_block,
    ``Physics.SixQuarkConventionalCoordinates.probes_O1,
    ``Physics.SixQuarkConventionalCoordinates.probes_O2,
    ``Physics.SixQuarkConventionalCoordinates.probes_O3,
    ``Physics.SixQuarkConventionalCoordinates.conventional_determinant,
    ``Physics.SixQuarkConventionalCoordinates.fierz,
    ``Physics.SixQuarkConventionalCoordinates.conventionalEquiv,
    ``Physics.SixQuarkConventionalCoordinates.reconstruct,
    ``Physics.SixQuarkConventionalCoordinates.probes_Q1,
    ``Physics.SixQuarkConventionalCoordinates.probes_Q4,
    ``Physics.SixQuarkConventionalCoordinates.chiralEquiv,
    ``Physics.SixQuarkConventionalCoordinates.reconstruct_chiral,
    ``Physics.SixQuarkGrassmannNormalization.pairing_ordered,
    ``Physics.SixQuarkGrassmannNormalization.ordered_eq_sector,
    ``Physics.SixQuarkGrassmannNormalization.basis_independent,
    ``Physics.SixQuarkGrassmannNormalization.O1_fourComponent,
    ``Physics.SixQuarkGrassmannNormalization.O2_fourComponent,
    ``Physics.SixQuarkGrassmannNormalization.O3_fourComponent,
    ``Physics.SixQuarkGrassmannNormalization.grassmann_reconstruct,
    ``Physics.SixQuarkGrassmannNormalization.grassmann_reconstruct_chiral,
    ``Physics.SixQuarkGrassmannNormalization.ordered_monomial,
    ``Physics.SixQuarkGrassmannNormalization.species_factorial,
    ``Physics.SixQuarkGrassmannNormalization.normalized_polynomial,
    ``Physics.SixQuarkGrassmannNormalization.species_block_sign]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Conventional six-quark checkpoint: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Conventional six-quark checkpoint: {declarations.length} strict transitive checks passed"
