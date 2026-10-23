import Math.RepresentationTheory.Weights.CyclicChargeOrbits
import Physics.StandardModel.Operators.Dipole.CyclicBasisDipoleSelection
import Physics.StandardModel.Operators.Selection.InverseCyclicSectorProperties
import Physics.StandardModel.Operators.Selection.InverseCyclicChargeOrbits
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
    ``Physics.CyclicBasisDipoleSelection.matrixUnit,
    ``Physics.CyclicBasisDipoleSelection.matrixUnit_selected,
    ``Physics.CyclicBasisDipoleSelection.selected_allowed_iff,
    ``Physics.CyclicBasisDipoleSelection.selected_forbidden_iff,
    ``Physics.InverseCyclicSectorProperties.six_quark_forbidden_iff,
    ``Physics.InverseCyclicSectorProperties.llhh_forbidden_iff,
    ``Physics.InverseCyclicSectorProperties.six_quark_allowed_iff,
    ``Physics.InverseCyclicSectorProperties.llhh_allowed_iff,
    ``Physics.InverseCyclicSectorProperties.profileCount,
    ``Physics.InverseCyclicSectorProperties.profile_counts,
    ``Physics.InverseCyclicChargeOrbits.preserves_bnv,
    ``Physics.InverseCyclicChargeOrbits.preserves_b2,
    ``Physics.InverseCyclicChargeOrbits.preserves_llhh,
    ``Physics.InverseCyclicChargeOrbits.orbitClasses,
    ``Physics.InverseCyclicChargeOrbits.orbit_counts,
    ``Physics.InverseCyclicChargeOrbits.total_orbits,
    ``Physics.InverseCyclicChargeOrbits.effectiveCount,
    ``Physics.InverseCyclicChargeOrbits.effective_counts]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Inverse cyclic follow-ups: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Inverse cyclic follow-ups: {ds.length} strict transitive checks passed"
