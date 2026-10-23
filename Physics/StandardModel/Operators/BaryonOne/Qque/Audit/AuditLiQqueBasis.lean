import Physics.StandardModel.Operators.BaryonOne.Qque.LiQqueCoordinates
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

/-! Strict trust and source-layer audit for the literal normalized D.38 pilot. -/
run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Li qque basis imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Physics.QqueResidualHom.equiv_symm_tprod,
    ``Physics.LiQqueConvention.ucDaggerEquiv,
    ``Physics.LiQqueConvention.ecDaggerEquiv,
    ``Physics.LiQqueConvention.singletSwap,
    ``Physics.LiQqueConvention.paperOrdered_apply,
    ``Physics.LiQqueConvention.fermionic_reorder,
    ``Physics.LiQqueConvention.candidate_eq,
    ``Physics.LiQqueConvention.candidate_probe,
    ``Physics.LiQqueConvention.equiv,
    ``Physics.LiQqueConvention.equiv_apply,
    ``Physics.LiQqueConvention.candidate_fromHom_eq,
    ``Physics.LiQqueConvention.onDaggerFieldsEquiv,
    ``Physics.LiQqueConvention.daggerTransport,
    ``Physics.LiQqueConvention.onDaggerFields_candidate,
    ``Physics.LiQqueCoordinates.matrixEquiv,
    ``Physics.LiQqueCoordinates.homEquiv,
    ``Physics.LiQqueCoordinates.mem_matrixSpace_iff,
    ``Physics.LiQqueCoordinates.homEquiv_entry,
    ``Physics.LiQqueCoordinates.residual_entry,
    ``Physics.LiQqueCoordinates.sectorEquiv,
    ``Physics.LiQqueCoordinates.inverse_left,
    ``Physics.LiQqueCoordinates.inverse_right,
    ``Physics.LiQqueCoordinates.inverse_is_candidate,
    ``Physics.LiQqueCoordinates.trivialHomEquiv,
    ``Physics.LiQqueCoordinates.flavorEquiv,
    ``Physics.LiQqueCoordinates.flavor_inverse_left,
    ``Physics.LiQqueCoordinates.flavor_inverse_right,
    ``Physics.LiQqueCoordinates.flavorBasis,
    ``Physics.LiQqueCoordinates.flavorBasis_is_candidate,
    ``Physics.LiQqueCoordinates.flavorBasis_independent,
    ``Physics.LiQqueCoordinates.flavorBasis_spans,
    ``Physics.LiQqueCoordinates.flavor_entry,
    ``Physics.LiQqueCoordinates.flavor_index_card,
    ``Physics.LiQqueCoordinates.flavor_paperOrdered_apply]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Li qque basis: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Li qque basis: {declarations.length} strict axiom checks passed"

-- Finite-flavor size controls supplement, rather than replace, the two inverses.
example : Fintype.card ((Fin 3 × Fin 3) × Sym (Fin 3) 2) = 54 := by
  rw [Physics.LiQqueCoordinates.flavor_index_card]
  norm_num [Nat.multichoose]
example : Fintype.card ((Fin 1 × Fin 1) × Sym (Fin 1) 2) = 1 := by
  rw [Physics.LiQqueCoordinates.flavor_index_card]
  norm_num [Nat.multichoose]
example : Fintype.card ((Fin 0 × Fin 3) × Sym (Fin 3) 2) = 0 := by
  rw [Physics.LiQqueCoordinates.flavor_index_card]
  norm_num [Nat.multichoose]
