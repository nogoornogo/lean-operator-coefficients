import GUT.PatiSalam.Matching.InvariantAction
import GUT.PatiSalam.Matching.UVGaugeCore
import GUT.PatiSalam.Matching.DisplayedKernelComparison
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod && !(`GUT.PatiSalam).isPrefixOf mod then
      throwError "PS action comparison imports another model {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``GUT.PatiSalam.InvariantAction.hermitian_unitary,
    ``GUT.PatiSalam.InvariantAction.contraction_tmul,
    ``GUT.PatiSalam.InvariantAction.chi_invariant,
    ``GUT.PatiSalam.InvariantAction.chi_array_invariant,
    ``GUT.PatiSalam.InvariantAction.phi_covariant,
    ``GUT.PatiSalam.InvariantAction.phiYukawa_invariant,
    ``GUT.PatiSalam.InvariantAction.phi_array,
    ``GUT.PatiSalam.InvariantAction.phiYukawa_array,
    ``GUT.PatiSalam.UVGaugeCore.eps4_invariant,
    ``GUT.PatiSalam.UVGaugeCore.rr_invariant,
    ``GUT.PatiSalam.UVGaugeCore.lr_invariant,
    ``GUT.PatiSalam.UVGaugeCore.eps4_color,
    ``GUT.PatiSalam.UVGaugeCore.selected_four,
    ``GUT.PatiSalam.UVGaugeCore.selected_basis,
    ``GUT.PatiSalam.UVGaugeCore.leftSelected_eq,
    ``GUT.PatiSalam.UVGaugeCore.selected_prefactor,
    ``GUT.PatiSalam.DisplayedKernelComparison.rescaled_vertex,
    ``GUT.PatiSalam.DisplayedKernelComparison.rescaled_mixing,
    ``GUT.PatiSalam.DisplayedKernelComparison.rescaled_norm_discrepancy,
    ``GUT.PatiSalam.DisplayedKernelComparison.mode_kernel_iff,
    ``GUT.PatiSalam.DisplayedKernelComparison.common_scale_mode_kernel_iff,
    ``GUT.PatiSalam.DisplayedKernelComparison.displayed_common_scale_not_kernel,
    ``GUT.PatiSalam.DisplayedKernelComparison.displayed_mode_not_kernel,
    ``GUT.PatiSalam.DisplayedKernelComparison.displayed_normalized_not_kernel]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "PS action comparison {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"PS action comparison: model boundary and {ds.length} strict transitive checks passed"
