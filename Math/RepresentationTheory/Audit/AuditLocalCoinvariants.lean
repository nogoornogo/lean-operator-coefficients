import Math.RepresentationTheory.LocalCoinvariantTensor
import Math.RepresentationTheory.CommutingActionHom

open Lean in
run_cmd do
  let ds := [
    ``Math.LocalCoinvariantHom.stable,
    ``Math.LocalCoinvariantHom.invariant_eq_vanishing,
    ``Math.LocalCoinvariantHom.equiv,
    ``Math.LocalCoinvariantHom.equiv_mk,
    ``Math.LocalCoinvariantHom.equiv_symm_apply,
    ``Math.LocalCoinvariantHom.forbidden_iff,
    ``Math.LocalCoinvariantHom.nonzero_iff,
    ``Math.LocalCoinvariantHom.map_relations,
    ``Math.LocalCoinvariantHom.descendExchange,
    ``Math.LocalCoinvariantHom.descendExchange_mk,
    ``Math.LocalCoinvariantTensor.tmul_mem,
    ``Math.LocalCoinvariantTensor.relations_eq_range,
    ``Math.LocalCoinvariantTensor.equiv,
    ``Math.LocalCoinvariantTensor.equiv_tmul_mk,
    ``Math.LocalCoinvariantTensor.residualEquiv,
    ``Math.CommutingActionHom.action,
    ``Math.CommutingActionHom.invariantEquiv,
    ``Math.CommutingActionHom.equiv,
    ``Math.CommutingActionHom.equiv_mk]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Local coinvariants {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Local coinvariants: {ds.length} strict transitive checks passed"
