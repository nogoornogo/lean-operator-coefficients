import Math.Audit.ImportOrigin
import PhyslibAlpha.Mathematics.ExteriorAlgebra
import Math.LinearAlgebra.Symmetric.PhyslibSymmetricDerivations
import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality

/-! Narrow Physlib connection: even algebra derivations and their covariance, with
a namespaced symmetric fragment co-imported with TauCeti functoriality.
This does not import or certify the external SM jet or analytic IBP packages. -/
open Lean in
run_cmd do
  let env ← getEnv
  let external := [
    `PhyslibAlpha.Mathematics.ExteriorAlgebra]
  for mod in env.header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Physlib algebra connection imports forbidden layer {mod}; original {SourceLayout.originalModule mod}"
    if ((`Physlib).isPrefixOf mod || (`PhyslibAlpha).isPrefixOf mod) &&
        !external.contains mod then
      throwError "Physlib algebra connection imports unexpected external module {mod}"
  for mod in [`PhyslibAlpha.Mathematics.ExteriorAlgebra,
      `Math.LinearAlgebra.Symmetric.PhyslibSymmetricDerivations,
      `TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality] do
    unless env.header.moduleNames.contains mod do
      throwError "Physlib connection misses required compatibility module {mod}"
  let ds := [
    ``ExteriorAlgebra.derivationOfLinear,
    ``ExteriorAlgebra.derivationOfLinear_ι,
    ``ExteriorAlgebra.derivationOfLinear_mul,
    ``ExteriorAlgebra.derivationOfLinear_comm_apply,
    ``ExteriorAlgebra.exteriorAlgebra_derivationOfLinear,
    ``Representation.exteriorAlgebra,
    ``Math.PhyslibSymmetric.SymmetricAlgebra.derivationOfLinear,
    ``Math.PhyslibSymmetric.SymmetricAlgebra.derivationOfLinear_ι,
    ``Math.PhyslibSymmetric.SymmetricAlgebra.derivationOfLinear_mul,
    ``Math.PhyslibSymmetric.SymmetricAlgebra.derivationOfLinear_comm_apply,
    ``Math.PhyslibSymmetric.SymmetricAlgebra.symmetricAlgebra_derivationOfLinear,
    ``Math.PhyslibSymmetric.Representation.symmetricAlgebra]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Physlib algebra connection {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Physlib algebra connection: {ds.length} strict transitive checks passed"
