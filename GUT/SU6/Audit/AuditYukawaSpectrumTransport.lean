import GUT.SU6.Yukawa.ResidualSinglets
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [``GUT.SU6YukawaCoordinates.label_bijective,
    ``GUT.SU6YukawaCoordinates.indexEquiv, ``GUT.SU6YukawaCoordinates.assemble,
    ``GUT.SU6YukawaCoordinates.coordinates, ``GUT.SU6YukawaCoordinates.coordinate_dual,
    ``GUT.SU6YukawaCoordinates.coordinate_exterior,
    ``GUT.SU6YukawaCoordinates.coordinates_triple,
    ``GUT.SU6YukawaCoordinates.coordinates_singlet, ``GUT.SU6YukawaCoordinates.kernel_iff,
    ``GUT.SU6YukawaCoordinates.radicalBlockEquiv, ``GUT.SU6YukawaCoordinates.radical_finrank,
    ``GUT.SU6YukawaCoordinates.radical_finrank_cases,
    ``GUT.SU6YukawaCoordinates.all_yukawa_dimensions,
    ``GUT.SU6YukawaCoordinates.all_nonzero_dimension_sixteen,
    ``GUT.SU6YukawaSinglets.standard_last, ``GUT.SU6YukawaSinglets.dualProbe_fixed,
    ``GUT.SU6YukawaSinglets.pureSinglet_fixed, ``GUT.SU6YukawaSinglets.lift_injective,
    ``GUT.SU6YukawaSinglets.singlet_kernel_iff, ``GUT.SU6YukawaSinglets.embedding,
    ``GUT.SU6YukawaSinglets.embedding_injective, ``GUT.SU6YukawaSinglets.singlet_dimension,
    ``GUT.SU6YukawaSinglets.standard_sixth, ``GUT.SU6YukawaSinglets.singlet_coordinates_fixed,
    ``GUT.SU6YukawaSinglets.projection, ``GUT.SU6YukawaSinglets.singletSplit,
    ``GUT.SU6YukawaSinglets.trivialCopiesEquiv, ``GUT.SU6YukawaSinglets.scalar_irreducible,
    ``GUT.SU6YukawaSinglets.trivialCopiesSplit,
    ``GUT.SU6YukawaSinglets.projection_surjective, ``GUT.SU6YukawaSinglets.complement_dimension]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SU6 Yukawa spectrum transport: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"SU6 Yukawa spectrum transport: {declarations.length} strict axiom checks passed"
