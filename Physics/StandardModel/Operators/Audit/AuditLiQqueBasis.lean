import Physics.StandardModel.Operators.LiQqueCoordinates
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

/-! Strict trust and source-layer audit for the literal normalized D.38 pilot. -/
run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Li qque basis imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.QqueResidualHom.equiv_symm_tprod,
    ``GUT.LiQqueConvention.ucDaggerEquiv,
    ``GUT.LiQqueConvention.ecDaggerEquiv,
    ``GUT.LiQqueConvention.singletSwap,
    ``GUT.LiQqueConvention.paperOrdered_apply,
    ``GUT.LiQqueConvention.fermionic_reorder,
    ``GUT.LiQqueConvention.candidate_eq,
    ``GUT.LiQqueConvention.candidate_probe,
    ``GUT.LiQqueConvention.equiv,
    ``GUT.LiQqueConvention.equiv_apply,
    ``GUT.LiQqueConvention.candidate_fromHom_eq,
    ``GUT.LiQqueConvention.onDaggerFieldsEquiv,
    ``GUT.LiQqueConvention.daggerTransport,
    ``GUT.LiQqueConvention.onDaggerFields_candidate,
    ``GUT.LiQqueCoordinates.matrixEquiv,
    ``GUT.LiQqueCoordinates.homEquiv,
    ``GUT.LiQqueCoordinates.mem_matrixSpace_iff,
    ``GUT.LiQqueCoordinates.homEquiv_entry,
    ``GUT.LiQqueCoordinates.residual_entry,
    ``GUT.LiQqueCoordinates.sectorEquiv,
    ``GUT.LiQqueCoordinates.inverse_left,
    ``GUT.LiQqueCoordinates.inverse_right,
    ``GUT.LiQqueCoordinates.inverse_is_candidate,
    ``GUT.LiQqueCoordinates.trivialHomEquiv,
    ``GUT.LiQqueCoordinates.flavorEquiv,
    ``GUT.LiQqueCoordinates.flavor_inverse_left,
    ``GUT.LiQqueCoordinates.flavor_inverse_right,
    ``GUT.LiQqueCoordinates.flavorBasis,
    ``GUT.LiQqueCoordinates.flavorBasis_is_candidate,
    ``GUT.LiQqueCoordinates.flavorBasis_independent,
    ``GUT.LiQqueCoordinates.flavorBasis_spans,
    ``GUT.LiQqueCoordinates.flavor_entry,
    ``GUT.LiQqueCoordinates.flavor_index_card,
    ``GUT.LiQqueCoordinates.flavor_paperOrdered_apply]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Li qque basis: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Li qque basis: {declarations.length} strict axiom checks passed"

-- Finite-flavor size controls supplement, rather than replace, the two inverses.
example : Fintype.card ((Fin 3 × Fin 3) × Sym (Fin 3) 2) = 54 := by
  rw [GUT.LiQqueCoordinates.flavor_index_card]
  norm_num [Nat.multichoose]
example : Fintype.card ((Fin 1 × Fin 1) × Sym (Fin 1) 2) = 1 := by
  rw [GUT.LiQqueCoordinates.flavor_index_card]
  norm_num [Nat.multichoose]
example : Fintype.card ((Fin 0 × Fin 3) × Sym (Fin 3) 2) = 0 := by
  rw [GUT.LiQqueCoordinates.flavor_index_card]
  norm_num [Nat.multichoose]
