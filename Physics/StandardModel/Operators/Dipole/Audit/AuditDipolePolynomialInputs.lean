import Physics.StandardModel.Operators.Dipole.DipolePolynomialControls
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Dipole polynomial inputs import model layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.PolynomialSelectedPaths.eval_selected,
    ``Math.PolynomialSelectedPaths.coefficient,
    ``Math.PolynomialSelectedPaths.exists_nonzero_on_box_iff,
    ``Math.PolynomialSelectedPaths.exists_nonzero_on_box_iff_coefficient,
    ``Math.PolynomialSelectedPaths.exists_nonzero_iff_coefficient,
    ``Math.PolynomialSelectedPaths.monomial_coefficient,
    ``Math.PolynomialSelectedPaths.exists_nonzero_monomials_iff_path,
    ``Math.PolynomialSelectedPaths.pair_exists_nonzero_on_box_iff_coefficient,
    ``Math.PolynomialSelectedPaths.pair_exists_nonzero_monomials_iff_path,
    ``Physics.DipolePolynomialInputs.exists_nonzero_on_box_iff_coefficient,
    ``Physics.DipolePolynomialInputs.exists_nonzero_monomials_iff_path,
    ``Physics.DipolePolynomialInputs.realized_iff_coefficient_of_factorization,
    ``Physics.DipolePolynomialControls.selected,
    ``Physics.DipolePolynomialControls.not_isolates,
    ``Physics.DipolePolynomialControls.realized,
    ``Physics.DipolePolynomialControls.same_monomial_cancels]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Dipole polynomial inputs: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Dipole polynomial inputs: {declarations.length} strict transitive axiom checks passed"
