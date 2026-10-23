import Physics.FieldTheory.Mass.Flavor.FlavorMajoranaLine
import Physics.FieldTheory.Mass.Flavor.FlavorMajoranaDiagonal
import Physics.FieldTheory.Mass.Flavor.FlavorMajoranaUnitary
import Math.RepresentationTheory.Multiplicity.FlavorCandidate
import Lean.Util.CollectAxioms

open Math

/-! Strict transitive audit of candidate mixing, specified-data stabilizers,
residual Hom, and the zero/nonzero/zero-VEV classification controls. -/
run_cmd do
  let declarations := [
    ``Math.FamilyStabilizer.subgroup,
    ``Math.FamilyStabilizer.maximal,
    ``Math.FamilyStabilizer.comap,
    ``Math.FamilyStabilizer.zero,
    ``Math.FamilyStabilizer.restricted_fixed,
    ``Math.FamilyStabilizer.invariantHomEquiv,
    ``Math.FlavorCandidate.action,
    ``Math.FlavorCandidate.action_commutes,
    ``Math.FlavorCandidate.action_faithful,
    ``Math.FlavorCandidate.ofOperator,
    ``Math.FlavorCandidate.coordinates,
    ``Physics.FlavorStabilizer.mass_mem_iff,
    ``Physics.FlavorStabilizer.coupling_mem_iff,
    ``Physics.FlavorStabilizer.full_le_mass,
    ``Physics.FlavorStabilizer.defect_zero_iff,
    ``Physics.FlavorStabilizer.mass_iff_defect_at_vacuum,
    ``Physics.FlavorStabilizer.equality_iff_no_hidden_defect,
    ``Physics.FlavorStabilizer.defect_zero_of_generators,
    ``Physics.FlavorStabilizer.coupling_of_generating_masses,
    ``Physics.FlavorStabilizer.data_mem_iff,
    ``Physics.FlavorStabilizer.restrictedYukawa,
    ``Physics.FlavorStabilizer.restrictedVacuum,
    ``Physics.FlavorStabilizer.sector_mass,
    ``Physics.FlavorStabilizer.residualHomEquiv,
    ``Physics.FlavorMajoranaLine.form_symmetric,
    ``Physics.FlavorMajoranaLine.mem_iff,
    ``Physics.FlavorMajoranaLine.zero_subgroup,
    ``Physics.FlavorMajoranaLine.nonzero_subgroup,
    ``Physics.FlavorMajoranaLine.rootsHom_bijective,
    ``Physics.FlavorMajoranaLine.cyclicEquiv,
    ``Physics.FlavorMajoranaLine.nonzero_card,
    ``Physics.FlavorMajoranaLine.coupling_evaluation,
    ``Physics.FlavorMajoranaLine.coupling_subgroup,
    ``Physics.FlavorMajoranaLine.evaluated_subgroup,
    ``Physics.FlavorMajoranaLine.nonzero_vacuum,
    ``Physics.FlavorMajoranaLine.zero_vacuum,
    ``Physics.FlavorMajoranaLine.accidental_strict,
    ``Physics.FlavorMajoranaDiagonal.phaseAction,
    ``Physics.FlavorMajoranaDiagonal.form_symmetric,
    ``Physics.FlavorMajoranaDiagonal.mem_iff,
    ``Physics.FlavorMajoranaDiagonal.membership,
    ``Physics.FlavorMajoranaDiagonal.productEquiv,
    ``Physics.FlavorMajoranaDiagonal.zero_subgroup,
    ``Physics.FlavorMajoranaDiagonal.zeroFactorEquiv,
    ``Physics.FlavorMajoranaDiagonal.mixedEquiv,
    ``Physics.FlavorMajoranaDiagonal.nonzeroEquiv,
    ``Physics.FlavorMajoranaDiagonal.nonzero_card,
    ``Physics.FlavorMajoranaDiagonal.evaluation_le,
    ``Physics.FlavorMajoranaDiagonal.evaluation_eq,
    ``Physics.FlavorMajoranaDiagonal.evaluation_eq_iff,
    ``Physics.FlavorMajoranaDiagonal.coupling_evaluation,
    ``Physics.FlavorMajoranaDiagonal.coupling_subgroup,
    ``Physics.FlavorMajoranaDiagonal.residualHomEquiv,
    ``Physics.FlavorMajoranaDiagonal.residual_nonzero_iff,
    ``Physics.FlavorMajoranaUnitary.action,
    ``Physics.FlavorMajoranaUnitary.form_matrix,
    ``Physics.FlavorMajoranaUnitary.subgroup_eq,
    ``Physics.FlavorMajoranaUnitary.classification,
    ``Physics.FlavorMajoranaUnitary.residualHomEquiv,
    ``Physics.FlavorMajoranaUnitary.residual_nonzero_iff]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo m!"Flavor stabilizer: {declarations.length} strict transitive checks passed"
