import Math.RepresentationTheory.Multiplicity.CompactMultiplicityIndex
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod || (`Physics).isPrefixOf mod then
      throwError "Compact multiplicity index imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.CompactMultiplicityIndex.coordinates,
    ``Math.CompactMultiplicityIndex.normedAddCommGroup,
    ``Math.CompactMultiplicityIndex.normedSpace,
    ``Math.CompactMultiplicityIndex.basisEvaluation_injective,
    ``Math.CompactMultiplicityIndex.jointlyContinuous,
    ``Math.CompactMultiplicityIndex.index,
    ``Math.CompactMultiplicityIndex.exists_split_of_index_eq,
    ``Math.CompactMultiplicityIndex.exists_common_quotient]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Compact multiplicity index: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Compact multiplicity index: {declarations.length} strict axiom checks passed"
