import Physics.StandardModel.Operators.Support.Dimension.SMChargeDegreeBounds
import Lean.Util.CollectAxioms

run_cmd do
  let ds := [``Physics.SMChargeDegreeBounds.species_abs,
    ``Physics.SMChargeDegreeBounds.charge_degree,
    ``Physics.SMChargeDegreeBounds.selected_degree,
    ``Physics.SMChargeDegreeBounds.twiceDimension,
    ``Physics.SMChargeDegreeBounds.dimension_lower,
    ``Physics.SMChargeDegreeBounds.b1_six_fermions,
    ``Physics.SMChargeDegreeBounds.b1_dimension_nine,
    ``Physics.SMChargeDegreeBounds.signed_charge_linear,
    ``Physics.SMChargeDegreeBounds.residual_linear,
    ``Physics.SMChargeDegreeBounds.original_even,
    ``Physics.SMChargeDegreeBounds.original_parity,
    ``Physics.SMChargeDegreeBounds.original_lepton_lower,
    ``Physics.SMChargeDegreeBounds.original_degree_lower]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "charge degree audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"charge degree bounds: {ds.length} strict transitive checks passed"
