import Physics.StandardModel.Operators.SMMixedCompactCoefficients
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Mixed chirality SM audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.WeylIndependentAction.spin_paired, ``GUT.WeylIndependentAction.family_zero,
    ``GUT.WeylIndependentAction.family_conjugate, ``GUT.WeylIndependentAction.family_generates,
    ``GUT.WeylIndependentAction.spin_affine, ``GUT.SMMixedCompactWeyl.field_paired,
    ``GUT.SMMixedCompactWeyl.field_affine, ``GUT.SMMixedCompactWeyl.source_polynomial,
    ``GUT.SMMixedCompactWeyl.source_paired, ``GUT.SMMixedCompactWeyl.spin_branch,
    ``GUT.SMMixedCompactWeyl.field_spanned, ``GUT.SMMixedCompactWeyl.source_spanned,
    ``GUT.SMMixedCompactWeyl.action_polynomial, ``GUT.SMMixedCompactWeyl.action_spanned,
    ``GUT.SMMixedCompactWeyl.action_paired, ``GUT.SMMixedCompactWeyl.coefficient_fixed_iff,
    ``GUT.SMMixedCompactCoefficients.full_decomposition, ``GUT.SMMixedCompactCoefficients.fullEquiv,
    ``GUT.SMMixedCompactCoefficients.local_decomposition, ``GUT.SMMixedCompactCoefficients.localEquiv,
    ``GUT.SMMixedCompactCoefficients.kernelEquiv, ``GUT.SMMixedCompactCoefficients.kernel_dimension,
    ``GUT.SMMixedCompactCoefficients.allowed_iff, ``GUT.SMMixedCompactCoefficients.original_allowed_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Mixed chirality SM audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Mixed chirality SM audit: layer and {ds.length} strict transitive checks passed"
