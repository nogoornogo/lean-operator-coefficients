import GUT.SU6.Yukawa.IndependentCouplings
import Lean.Util.CollectAxioms

open Math

run_cmd do
  let declarations := [
    ``Math.SplitRepresentationProjection.prodEquiv_apply,
    ``GUT.SU6TwoBlockSpectrum.normalEquiv,
    ``GUT.SU6TwoBlockSpectrum.mass_apply,
    ``GUT.SU6TwoBlockSpectrum.fullRadicalEquiv,
    ``GUT.SU6TwoBlockSpectrum.five_probe,
    ``GUT.SU6TwoBlockSpectrum.singlet_probe,
    ``GUT.SU6TwoBlockSpectrum.radical_finrank,
    ``GUT.SU6TwoBlockSpectrum.mass_eq_iff,
    ``GUT.SU6IndependentCouplings.baseYukawa,
    ``GUT.SU6IndependentCouplings.baseYukawa_vacuum,
    ``GUT.SU6IndependentCouplings.exteriorProjection,
    ``GUT.SU6IndependentCouplings.coupling,
    ``GUT.SU6IndependentCouplings.mass,
    ``GUT.SU6IndependentCouplings.branch_projection,
    ``GUT.SU6IndependentCouplings.branch_anti,
    ``GUT.SU6IndependentCouplings.original_pullback,
    ``GUT.SU6IndependentCouplings.transformed_bilinear,
    ``GUT.SU6IndependentCouplings.anti_eq_sub,
    ``GUT.SU6IndependentCouplings.transformed_complement,
    ``GUT.SU6IndependentCouplings.projected_mass_form,
    ``GUT.SU6IndependentCouplings.mass_eq,
    ``GUT.SU6IndependentCouplings.fullRadicalEquiv,
    ``GUT.SU6IndependentCouplings.mass_eq_iff,
    ``GUT.SU6IndependentCouplings.coupling_eq_iff,
    ``GUT.SU6IndependentCouplings.radical_finrank,
    ``GUT.SU6IndependentCouplings.fifteen,
    ``GUT.SU6IndependentCouplings.seventeen,
    ``GUT.SU6IndependentCouplings.twentyFive,
    ``GUT.SU6IndependentCouplings.twentySeven]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Independent SU6 Yukawa family: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Independent SU6 Yukawa family: {declarations.length} strict axiom checks passed"
