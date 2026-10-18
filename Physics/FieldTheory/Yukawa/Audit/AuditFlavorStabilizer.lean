import Physics.FieldTheory.Mass.FlavorMajoranaLine
import Physics.FieldTheory.Mass.FlavorMajoranaDiagonal
import Physics.FieldTheory.Mass.FlavorMajoranaUnitary
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
    ``GUT.FlavorStabilizer.mass_mem_iff,
    ``GUT.FlavorStabilizer.coupling_mem_iff,
    ``GUT.FlavorStabilizer.full_le_mass,
    ``GUT.FlavorStabilizer.defect_zero_iff,
    ``GUT.FlavorStabilizer.mass_iff_defect_at_vacuum,
    ``GUT.FlavorStabilizer.equality_iff_no_hidden_defect,
    ``GUT.FlavorStabilizer.defect_zero_of_generators,
    ``GUT.FlavorStabilizer.coupling_of_generating_masses,
    ``GUT.FlavorStabilizer.data_mem_iff,
    ``GUT.FlavorStabilizer.restrictedYukawa,
    ``GUT.FlavorStabilizer.restrictedVacuum,
    ``GUT.FlavorStabilizer.sector_mass,
    ``GUT.FlavorStabilizer.residualHomEquiv,
    ``GUT.FlavorMajoranaLine.form_symmetric,
    ``GUT.FlavorMajoranaLine.mem_iff,
    ``GUT.FlavorMajoranaLine.zero_subgroup,
    ``GUT.FlavorMajoranaLine.nonzero_subgroup,
    ``GUT.FlavorMajoranaLine.rootsHom_bijective,
    ``GUT.FlavorMajoranaLine.cyclicEquiv,
    ``GUT.FlavorMajoranaLine.nonzero_card,
    ``GUT.FlavorMajoranaLine.coupling_evaluation,
    ``GUT.FlavorMajoranaLine.coupling_subgroup,
    ``GUT.FlavorMajoranaLine.evaluated_subgroup,
    ``GUT.FlavorMajoranaLine.nonzero_vacuum,
    ``GUT.FlavorMajoranaLine.zero_vacuum,
    ``GUT.FlavorMajoranaLine.accidental_strict,
    ``GUT.FlavorMajoranaDiagonal.phaseAction,
    ``GUT.FlavorMajoranaDiagonal.form_symmetric,
    ``GUT.FlavorMajoranaDiagonal.mem_iff,
    ``GUT.FlavorMajoranaDiagonal.membership,
    ``GUT.FlavorMajoranaDiagonal.productEquiv,
    ``GUT.FlavorMajoranaDiagonal.zero_subgroup,
    ``GUT.FlavorMajoranaDiagonal.zeroFactorEquiv,
    ``GUT.FlavorMajoranaDiagonal.mixedEquiv,
    ``GUT.FlavorMajoranaDiagonal.nonzeroEquiv,
    ``GUT.FlavorMajoranaDiagonal.nonzero_card,
    ``GUT.FlavorMajoranaDiagonal.evaluation_le,
    ``GUT.FlavorMajoranaDiagonal.evaluation_eq,
    ``GUT.FlavorMajoranaDiagonal.evaluation_eq_iff,
    ``GUT.FlavorMajoranaDiagonal.coupling_evaluation,
    ``GUT.FlavorMajoranaDiagonal.coupling_subgroup,
    ``GUT.FlavorMajoranaDiagonal.residualHomEquiv,
    ``GUT.FlavorMajoranaDiagonal.residual_nonzero_iff,
    ``GUT.FlavorMajoranaUnitary.action,
    ``GUT.FlavorMajoranaUnitary.form_matrix,
    ``GUT.FlavorMajoranaUnitary.subgroup_eq,
    ``GUT.FlavorMajoranaUnitary.classification,
    ``GUT.FlavorMajoranaUnitary.residualHomEquiv,
    ``GUT.FlavorMajoranaUnitary.residual_nonzero_iff]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo m!"Flavor stabilizer: {declarations.length} strict transitive checks passed"
