import Math.Audit.ImportOrigin
import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsUpper
import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveSum
import Physics.FieldTheory.Jets.WeylDirectionInvariant.Core.Tensor
import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsCompleteLiterature

/-! Strict full-namespace and transitive helper inventories for the resumed
actual-source Lorentz reduction and full-relation wave sum. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  for ns in [`Physics.WeylDirectionInvariant, `Physics.WeylHiggsFirstTensor,
      `Physics.WeylHiggsFirstSource, `Physics.WeylHiggsLorentzUpper, `Physics.WeylHiggsWaveSum,
      `Physics.HiggsFirstInternal, `Physics.WeylHiggsInternalLift,
      `Physics.WeylHiggsEvenValue, `Physics.WeylHiggsUpper,
      `Physics.WeylHiggsWaveWords, `Physics.WeylHiggsWaveMoments,
      `Physics.WeylHiggsWaveLorentz, `Physics.WeylHiggsWaveInternalFields,
      `Physics.WeylHiggsWaveInternal, `Physics.WeylHiggsWaveInvariant,
      `Physics.WeylHiggsCompleteness, `Physics.WeylHiggsCompleteLiterature] do
    let mut checked : Nat := 0
    for (d, _) in env.constants.toList do
      if ns.isPrefixOf d then
        checked := checked + 1
        for ax in (← Lean.collectAxioms d) do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
            throwError "Declaration {d} uses unexpected axiom {ax}"
    unless checked > 0 do throwError "Empty first-completion inventory: {ns}"
    Lean.logInfo m!"{ns}: {checked} strict transitive declaration checks passed"
