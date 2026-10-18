import GUT.SU5.SelectionRules.GeorgiGlashowQque
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.SU5.GeorgiGlashowSource.compatible,
    ``GUT.SU5.GeorgiGlashowSource.radicalEquiv,
    ``GUT.SU5.GeorgiGlashowSource.spectrumEquiv,
    ``GUT.SU5.GeorgiGlashowSource.actualSpectrumEquiv,
    ``GUT.SU5.GeorgiGlashowSource.hasSpectrum,
    ``GUT.SU5.GeorgiGlashowSource.torus_unitary,
    ``GUT.SU5.GeorgiGlashowSource.compatible_continuous,
    ``GUT.SU5.GeorgiGlashowSource.exists_actual_exterior,
    ``GUT.SU5.GeorgiGlashowQque.shared_positive,
    ``GUT.SU5.GeorgiGlashowQque.pairwise_positive,
    ``GUT.SU5.GeorgiGlashowQque.exists_actual_alternation,
    ``GUT.SU5.GeorgiGlashowQque.exists_actual_exterior,
    ``GUT.SU5.GeorgiGlashowBenchmark.species_counts,
    ``GUT.SU5.GeorgiGlashowBenchmark.one_generation_exterior,
    ``GUT.SU5.GeorgiGlashowBenchmark.three_generation_exterior]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Georgi-Glashow qque: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Georgi-Glashow qque: {declarations.length} strict axiom checks passed"
