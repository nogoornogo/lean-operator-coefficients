import Math.Audit.ImportOrigin
import Math.Algebra.Jets.LinearJetKernel
import Math.Algebra.Jets.LinearJetSingleField
import Math.Algebra.Jets.JetConjugation
import Math.Algebra.Jets.JetExteriorAdjoint

/-! Strict transitive standard-axiom and import-layer audit. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Math.LinearJetAlgebra.relationIdeal,
    ``Math.LinearJetAlgebra.relationIdeal_le_kernel,
    ``Math.LinearJetAlgebra.kernel_eq_relationIdeal,
    ``Math.LinearJetAlgebra.descendantIdeal,
    ``Math.LinearJetAlgebra.descendantIdeal_eq,
    ``Math.LinearJetAlgebra.kernel_eq_descendantIdeal,
    ``Math.LinearJetAlgebra.odd_offRelations_top,
    ``Math.LinearJetAlgebra.odd_ibpRelations_top,
    ``Math.LinearJetAlgebra.odd_quotient_subsingleton,
    ``Math.LinearJetAlgebra.odd_quotient_finrank,
    ``Math.LinearJetAlgebra.odd_quotient_basis,
    ``Math.JetConjugation.coefficients,
    ``Math.JetConjugation.coefficients_apply,
    ``Math.JetConjugation.coefficients_single,
    ``Math.JetConjugation.coefficients_involutive,
    ``Math.JetConjugation.symbols,
    ``Math.JetConjugation.coefficients_ofSymbols,
    ``Math.JetConjugation.coefficients_multiple,
    ``Math.JetConjugation.coefficients_shift,
    ``Math.JetConjugation.coefficients_atOrder,
    ``Math.JetConjugation.coefficients_internal,
    ``Math.JetConjugation.symbols_linearForm,
    ``Math.JetConjugation.symbols_symbolMap,
    ``Math.JetConjugation.coefficients_direction,
    ``Math.JetExteriorAdjoint.map,
    ``Math.JetExteriorAdjoint.map_generator,
    ``Math.JetExteriorAdjoint.map_scalar,
    ``Math.JetExteriorAdjoint.map_mul,
    ``Math.JetExteriorAdjoint.involutive,
    ``Math.JetExteriorAdjoint.naturality,
    ``Math.JetExteriorAdjoint.derivative,
    ``Math.JetExteriorAdjoint.divergence,
    ``Math.JetExteriorAdjoint.divergence_single,
    ``Math.JetExteriorAdjoint.relations,
    ``Math.JetExteriorAdjoint.stable,
    ``Math.JetExteriorAdjoint.quotient,
    ``Math.JetExteriorAdjoint.quotient_mk,
    ``Math.JetExteriorAdjoint.quotient_involutive]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Declaration {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Jet EOM completion: {ds.length} strict transitive checks passed"
