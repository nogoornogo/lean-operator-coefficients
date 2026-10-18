import Math.RepresentationTheory.Multiplicity.FiniteSpectrum
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

namespace Math.FiniteSpectrumAudit
noncomputable section
open Representation FiniteSpectrum

theorem zero_copies :
    Module.finrank ℂ (IntertwiningMap (Representation.trivial ℂ Unit ℂ)
      (copies 0 (Representation.trivial ℂ Unit ℂ))) = 0 := by
  rw [hom_finrank_copies, zero_mul]

end
end Math.FiniteSpectrumAudit

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Finite spectrum math audit imports {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.FiniteSpectrum.copies,
    ``Math.FiniteSpectrum.character_copies,
    ``Math.FiniteSpectrum.homProd,
    ``Math.FiniteSpectrum.homCopies,
    ``Math.FiniteSpectrum.homCongrRight,
    ``Math.FiniteSpectrum.hom_finrank_prod,
    ``Math.FiniteSpectrum.hom_finrank_copies,
    ``Math.FiniteSpectrum.intertwiner_eq_zero_of_scalar,
    ``Math.FiniteSpectrumAudit.zero_copies]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Finite spectrum: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Finite spectrum: {declarations.length} strict axiom checks passed"
