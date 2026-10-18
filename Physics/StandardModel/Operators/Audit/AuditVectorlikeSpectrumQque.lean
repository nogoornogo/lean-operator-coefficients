import Physics.StandardModel.Operators.VectorlikeSpectrumQque
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Vectorlike spectrum imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.VectorlikeMultiplicity.balance,
    ``Math.VectorlikeMultiplicity.extension,
    ``GUT.VectorlikeSpectrumQque.extension,
    ``GUT.VectorlikeSpectrumQque.shared_positive,
    ``GUT.VectorlikeSpectrumQque.exists_actual_exterior]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Vectorlike spectrum: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Vectorlike spectrum: {declarations.length} strict axiom checks passed"
