import GUT.SU6.Yukawa.VacuumImage
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [``GUT.SU6YukawaStabilizer.inverse_sixth,
    ``GUT.SU6YukawaStabilizer.heavyVector_covariant,
    ``GUT.SU6YukawaStabilizer.mass_fixed, ``GUT.SU6YukawaStabilizer.vacuum_fixed,
    ``GUT.SU6YukawaStabilizer.phaseElement, ``GUT.SU6YukawaStabilizer.phase_action,
    ``GUT.SU6YukawaStabilizer.phase_vacuum, ``GUT.SU6YukawaStabilizer.swapElement,
    ``GUT.SU6YukawaStabilizer.swap_action, ``GUT.SU6YukawaStabilizer.swap_vacuum,
    ``GUT.SU6YukawaStabilizer.evaluation_fixed, ``GUT.SU6YukawaStabilizer.evaluation_phase,
    ``GUT.SU6YukawaStabilizer.evaluation_swap,
    ``GUT.SU6YukawaWeights.allowed_cases, ``GUT.SU6YukawaWeights.separation,
    ``GUT.SU6YukawaWeights.character_add, ``GUT.SU6YukawaWeights.character_eq_one,
    ``GUT.SU6YukawaWeights.character_neg, ``GUT.SU6YukawaWeights.allowed_iff,
    ``GUT.SU6YukawaBasis.basis, ``GUT.SU6YukawaBasis.exteriorBasis_coordinates,
    ``GUT.SU6YukawaBasis.dualBasis_coordinates, ``GUT.SU6YukawaBasis.phase_character,
    ``GUT.SU6YukawaBasis.exterior_phase, ``GUT.SU6YukawaBasis.dual_phase,
    ``GUT.SU6YukawaBasis.basis_phase, ``GUT.SU6YukawaBasis.entry_zero_of,
    ``GUT.SU6YukawaBasis.evaluation_entry_zero,
    ``GUT.SU6YukawaBasis.exterior_swap, ``GUT.SU6YukawaBasis.dual_swap,
    ``GUT.SU6YukawaBasis.exteriorLabel_swap, ``GUT.SU6YukawaBasis.dualLabel_swap,
    ``GUT.SU6YukawaBasis.channel_eq, ``GUT.SU6YukawaBasis.eq_of_entries,
    ``GUT.SU6YukawaImage.dualBasis_probe, ``GUT.SU6YukawaImage.exteriorBasis_probe,
    ``GUT.SU6YukawaImage.basis_probeQ, ``GUT.SU6YukawaImage.basis_probeA,
    ``GUT.SU6YukawaImage.basis_probeB, ``GUT.SU6YukawaImage.evaluation_eq_of_probes,
    ``GUT.SU6YukawaImage.coupling_evaluation, ``GUT.SU6YukawaImage.evaluation_mem_range,
    ``GUT.SU6YukawaImage.realized_iff]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SU6 Yukawa vacuum image: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"SU6 Yukawa vacuum image: {declarations.length} strict axiom checks passed"
