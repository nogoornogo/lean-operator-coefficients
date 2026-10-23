import Math.Audit.ImportOrigin
import Math.Algebra.Constructions.ColoredQuarticSource
import Math.Algebra.Waves.ColoredFourWavePolarization
import Math.Algebra.Constructions.FourDerivativeWords
import Math.Algebra.Waves.HiggsFourWaveCubature
import Math.Algebra.HiggsFourWaveCubature.Contractions
import Math.LinearAlgebra.Constructions.SevenScalarConstraints
import Math.RepresentationTheory.Color.Diagrams.ColoredWavePairing
import Math.RepresentationTheory.Relations.SelectedRelationExtension
import Math.RepresentationTheory.Jets.DerivativeLiteratureLiHiggs

/-! Nonempty whole-namespace strict transitive axiom and layer inventories. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  for ns in [`Math.ColoredDegreeFour,
      `Math.ColoredQuarticWords,
      `Math.ColoredQuarticSource,
      `Math.ColoredFourWavePolarization,
      `Math.FourDerivativeWords,
      `Math.HiggsFourWaveCubature,
      `Math.SevenScalarConstraints,
      `Math.ColoredWavePairing,
      `Math.SelectedRelationExtension,
      `Math.DerivativeLiteratureLiHiggs] do
    let mut checked : Nat := 0
    for (d, _) in env.constants.toList do
      if ns.isPrefixOf d then
        checked := checked + 1
        for ax in (← Lean.collectAxioms d) do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
            throwError "Declaration {d} uses unexpected axiom {ax}"
    unless checked > 0 do throwError "Empty Higgs completeness inventory: {ns}"
    Lean.logInfo m!"{ns}: {checked} strict transitive declaration checks passed"
