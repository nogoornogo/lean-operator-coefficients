import Physics.FieldTheory.Yukawa.YukawaClassification
import Physics.FieldTheory.Mass.ScaledMassSpectrum
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.YukawaClassification.toMap,
    ``GUT.YukawaClassification.ofMap,
    ``GUT.YukawaClassification.ofMap_toMap,
    ``GUT.YukawaClassification.toMap_ofMap,
    ``GUT.YukawaClassification.equiv,
    ``GUT.YukawaClassification.endomorphismEquiv,
    ``GUT.YukawaClassification.evaluation,
    ``GUT.YukawaClassification.scalarMultiple,
    ``GUT.ScaledMassSpectrum.mass,
    ``GUT.ScaledMassSpectrum.zero_mass,
    ``GUT.ScaledMassSpectrum.one_mass,
    ``GUT.ScaledMassSpectrum.form_nonzero,
    ``GUT.ScaledMassSpectrum.mem_radical_iff,
    ``GUT.ScaledMassSpectrum.radicalEquiv,
    ``GUT.ScaledMassSpectrum.radical_finrank,
    ``GUT.ScaledMassSpectrum.radical_character]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Yukawa classification: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Yukawa classification: {declarations.length} strict axiom checks passed"
