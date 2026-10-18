import GUT.SU6.Yukawa.NonSingletSpectrum
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [``GUT.SU6NonSingletCoordinates.gaugeEquiv,
    ``GUT.SU6NonSingletCoordinates.withResidual, ``GUT.SU6NonSingletCoordinates.coords,
    ``GUT.SU6NonSingletCoordinates.coords_action,
    ``GUT.SU6NonSingletCoordinates.coords_five,
    ``GUT.SU6NonSingletCoordinates.coords_dual,
    ``GUT.SU6NonSingletCoordinates.coords_singlet,
    ``GUT.SU6NonSingletCoordinates.dual_zero_iff,
    ``GUT.SU6ResidualConstituents.dualFiveSplit,
    ``GUT.SU6ResidualConstituents.residualDualFiveSplit,
    ``GUT.SU6ResidualConstituents.factors_irreducible,
    ``GUT.SU6NonSingletSpectrum.radical_coordinates,
    ``GUT.SU6NonSingletSpectrum.radicalEquiv,
    ``GUT.SU6NonSingletSpectrum.nonzeroEquiv,
    ``GUT.SU6NonSingletSpectrum.zeroEquiv,
    ``GUT.SU6NonSingletSpectrum.nonzeroDecomposition,
    ``GUT.SU6NonSingletSpectrum.zeroDecomposition,
    ``GUT.SU6NonSingletSpectrum.all_yukawa_decompositions]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Non-singlet spectrum: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Non-singlet spectrum: {declarations.length} strict axiom checks passed"
