import Physics.StandardModel.Operators.SMChargeDegreeBounds
import Lean.Util.CollectAxioms

run_cmd do
  let ds := [``GUT.SMChargeDegreeBounds.species_abs,
    ``GUT.SMChargeDegreeBounds.charge_degree,
    ``GUT.SMChargeDegreeBounds.selected_degree,
    ``GUT.SMChargeDegreeBounds.twiceDimension,
    ``GUT.SMChargeDegreeBounds.dimension_lower,
    ``GUT.SMChargeDegreeBounds.b1_six_fermions,
    ``GUT.SMChargeDegreeBounds.b1_dimension_nine,
    ``GUT.SMChargeDegreeBounds.signed_charge_linear,
    ``GUT.SMChargeDegreeBounds.residual_linear,
    ``GUT.SMChargeDegreeBounds.original_even,
    ``GUT.SMChargeDegreeBounds.original_parity,
    ``GUT.SMChargeDegreeBounds.original_lepton_lower,
    ``GUT.SMChargeDegreeBounds.original_degree_lower]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "charge degree audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"charge degree bounds: {ds.length} strict transitive checks passed"
