import Physics.StandardModel.Operators.Dipole.DipoleCouplingControls
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
    ``Physics.DipoleCouplingModel.bilinear,
    ``Physics.DipoleCouplingModel.bilinear_apply,
    ``Physics.DipoleCouplingModel.generation_residual,
    ``Physics.DipoleCouplingModel.selected,
    ``Physics.DipoleCouplingModel.generation_zero_of_propagator_zero,
    ``Physics.DipoleCouplingModel.residual_expansion,
    ``Physics.DipoleCouplingModel.generation_factorization,
    ``Physics.DipoleCouplingModel.basis_paths,
    ``Physics.DipoleCouplingModel.generation_eq_paths,
    ``Physics.DipoleCouplingModel.exists_nonzero_iff_basis_path,
    ``Physics.DipoleCouplingModel.nonzero_at_basis_witness,
    ``Physics.DipoleCouplingModel.parameterized_factorization,
    ``Physics.DipoleCouplingControls.selected,
    ``Physics.DipoleCouplingControls.nonzero_iff,
    ``Physics.DipoleCouplingControls.zero_propagator,
    ``Physics.DipoleCouplingControls.nonlinear_pullback]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Dipole coupling model: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Dipole coupling model: {declarations.length} strict transitive axiom checks passed"
