import Physics.StandardModel.Operators.Support.Joint.SMMixedCompactCoefficients
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Mixed chirality SM audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.WeylIndependentAction.spin_paired, ``Physics.WeylIndependentAction.family_zero,
    ``Physics.WeylIndependentAction.family_conjugate, ``Physics.WeylIndependentAction.family_generates,
    ``Physics.WeylIndependentAction.spin_affine, ``Physics.SMMixedCompactWeyl.field_paired,
    ``Physics.SMMixedCompactWeyl.field_affine, ``Physics.SMMixedCompactWeyl.source_polynomial,
    ``Physics.SMMixedCompactWeyl.source_paired, ``Physics.SMMixedCompactWeyl.spin_branch,
    ``Physics.SMMixedCompactWeyl.field_spanned, ``Physics.SMMixedCompactWeyl.source_spanned,
    ``Physics.SMMixedCompactWeyl.action_polynomial, ``Physics.SMMixedCompactWeyl.action_spanned,
    ``Physics.SMMixedCompactWeyl.action_paired, ``Physics.SMMixedCompactWeyl.coefficient_fixed_iff,
    ``Physics.SMMixedCompactCoefficients.full_decomposition, ``Physics.SMMixedCompactCoefficients.fullEquiv,
    ``Physics.SMMixedCompactCoefficients.local_decomposition, ``Physics.SMMixedCompactCoefficients.localEquiv,
    ``Physics.SMMixedCompactCoefficients.kernelEquiv, ``Physics.SMMixedCompactCoefficients.kernel_dimension,
    ``Physics.SMMixedCompactCoefficients.allowed_iff, ``Physics.SMMixedCompactCoefficients.original_allowed_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Mixed chirality SM audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Mixed chirality SM audit: layer and {ds.length} strict transitive checks passed"
