import Physics.FieldTheory.Yukawa.Mass.YukawaClassification
import Physics.FieldTheory.Mass.Spectrum.ScaledMassSpectrum
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Physics.YukawaClassification.toMap,
    ``Physics.YukawaClassification.ofMap,
    ``Physics.YukawaClassification.ofMap_toMap,
    ``Physics.YukawaClassification.toMap_ofMap,
    ``Physics.YukawaClassification.equiv,
    ``Physics.YukawaClassification.endomorphismEquiv,
    ``Physics.YukawaClassification.evaluation,
    ``Physics.YukawaClassification.scalarMultiple,
    ``Physics.ScaledMassSpectrum.mass,
    ``Physics.ScaledMassSpectrum.zero_mass,
    ``Physics.ScaledMassSpectrum.one_mass,
    ``Physics.ScaledMassSpectrum.form_nonzero,
    ``Physics.ScaledMassSpectrum.mem_radical_iff,
    ``Physics.ScaledMassSpectrum.radicalEquiv,
    ``Physics.ScaledMassSpectrum.radical_finrank,
    ``Physics.ScaledMassSpectrum.radical_character]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Yukawa classification: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Yukawa classification: {declarations.length} strict axiom checks passed"
