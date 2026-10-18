import Math.RepresentationTheory.Decomposition.SpeciesCopySurplus
import Math.RepresentationTheory.Decomposition.ExternalCopyFactorization
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod then
      throwError "Unexpected upper-layer import: {mod}"
    if (`GUT).isPrefixOf mod then
      throwError "Unexpected upper-layer import: {mod}"
    let origin := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf origin || (`GUT.SU6).isPrefixOf origin then
      throwError "Unexpected original SU5/SU6 import: {mod}"
  let declarations := [
    ``Math.SpeciesCopySurplus.Surplus,
    ``Math.SpeciesCopySurplus.postcompose,
    ``Math.SpeciesCopySurplus.intoKernel,
    ``Math.SpeciesCopySurplus.homKernelEquiv,
    ``Math.SpeciesCopySurplus.exists_nonzero_kernel_map,
    ``Math.SpeciesCopySurplus.kernel_semisimple,
    ``Math.SpeciesCopySurplus.exists_kernel_split,
    ``Math.SpeciesCopySurplus.family_kernel_splits,
    ``Math.ExternalCopyFactorization.coordinates,
    ``Math.ExternalCopyFactorization.coordinates_tmul,
    ``Math.ExternalCopyFactorization.slice,
    ``Math.ExternalCopyFactorization.exists_copy_map]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom: {decl}: {ax}"
  Lean.logInfo m!"SpeciesCopySurplus math: {declarations.length} strict transitive checks; layer imports checked"
