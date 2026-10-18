import Math.RepresentationTheory.CyclicChargeOrbits
import Physics.StandardModel.Operators.CyclicBasisDipoleSelection
import Physics.StandardModel.Operators.InverseCyclicSectorProperties
import Physics.StandardModel.Operators.InverseCyclicChargeOrbits
import Lean.Util.CollectAxioms
run_cmd do
  let ds := [``Math.CyclicChargeOrbits.scale,
    ``Math.CyclicChargeOrbits.scale_one,
    ``Math.CyclicChargeOrbits.scale_mul,
    ``Math.CyclicChargeOrbits.Equivalent,
    ``Math.CyclicChargeOrbits.equivalent_refl,
    ``Math.CyclicChargeOrbits.equivalent_symm,
    ``Math.CyclicChargeOrbits.equivalent_trans,
    ``Math.CyclicChargeOrbits.orbit,
    ``Math.CyclicChargeOrbits.mem_orbit,
    ``Math.CyclicChargeOrbits.orbit_eq_iff,
    ``Math.CyclicChargeOrbits.linear_test,
    ``Math.CyclicChargeOrbits.phaseImage,
    ``Math.CyclicChargeOrbits.effectiveOrder,
    ``Math.CyclicChargeOrbits.phaseImage_scale,
    ``Math.CyclicChargeOrbits.effectiveOrder_scale,
    ``Math.CyclicChargeOrbits.phases,
    ``Math.CyclicChargeOrbits.phases_injective,
    ``Math.CyclicChargeOrbits.effectiveOrder_actual,
    ``Math.CyclicChargeOrbits.relabel,
    ``Math.CyclicChargeOrbits.relabeled_action,
    ``GUT.CyclicBasisDipoleSelection.matrixUnit,
    ``GUT.CyclicBasisDipoleSelection.matrixUnit_selected,
    ``GUT.CyclicBasisDipoleSelection.selected_allowed_iff,
    ``GUT.CyclicBasisDipoleSelection.selected_forbidden_iff,
    ``GUT.InverseCyclicSectorProperties.six_quark_forbidden_iff,
    ``GUT.InverseCyclicSectorProperties.llhh_forbidden_iff,
    ``GUT.InverseCyclicSectorProperties.six_quark_allowed_iff,
    ``GUT.InverseCyclicSectorProperties.llhh_allowed_iff,
    ``GUT.InverseCyclicSectorProperties.profileCount,
    ``GUT.InverseCyclicSectorProperties.profile_counts,
    ``GUT.InverseCyclicChargeOrbits.preserves_bnv,
    ``GUT.InverseCyclicChargeOrbits.preserves_b2,
    ``GUT.InverseCyclicChargeOrbits.preserves_llhh,
    ``GUT.InverseCyclicChargeOrbits.orbitClasses,
    ``GUT.InverseCyclicChargeOrbits.orbit_counts,
    ``GUT.InverseCyclicChargeOrbits.total_orbits,
    ``GUT.InverseCyclicChargeOrbits.effectiveCount,
    ``GUT.InverseCyclicChargeOrbits.effective_counts]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Inverse cyclic follow-ups: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Inverse cyclic follow-ups: {ds.length} strict transitive checks passed"
