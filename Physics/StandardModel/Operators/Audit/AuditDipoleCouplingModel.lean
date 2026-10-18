import Physics.StandardModel.Operators.DipoleCouplingControls
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Dipole coupling model imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.BilinearSelectedPaths.expansion,
    ``Math.BilinearSelectedPaths.weights_isolate,
    ``Math.BilinearSelectedPaths.exists_nonzero_iff_basis_path,
    ``Math.BilinearSelectedPaths.parameterized_expansion,
    ``GUT.DipoleCouplingModel.bilinear,
    ``GUT.DipoleCouplingModel.bilinear_apply,
    ``GUT.DipoleCouplingModel.generation_residual,
    ``GUT.DipoleCouplingModel.selected,
    ``GUT.DipoleCouplingModel.generation_zero_of_propagator_zero,
    ``GUT.DipoleCouplingModel.residual_expansion,
    ``GUT.DipoleCouplingModel.generation_factorization,
    ``GUT.DipoleCouplingModel.basis_paths,
    ``GUT.DipoleCouplingModel.generation_eq_paths,
    ``GUT.DipoleCouplingModel.exists_nonzero_iff_basis_path,
    ``GUT.DipoleCouplingModel.nonzero_at_basis_witness,
    ``GUT.DipoleCouplingModel.parameterized_factorization,
    ``GUT.DipoleCouplingControls.selected,
    ``GUT.DipoleCouplingControls.nonzero_iff,
    ``GUT.DipoleCouplingControls.zero_propagator,
    ``GUT.DipoleCouplingControls.nonlinear_pullback]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Dipole coupling model: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Dipole coupling model: {declarations.length} strict transitive axiom checks passed"
