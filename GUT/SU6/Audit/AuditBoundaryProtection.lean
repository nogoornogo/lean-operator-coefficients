import GUT.SU6.Boundary.Protection
import Lean.Util.CollectAxioms

/-! Strict transitive audit of the boundary construction and shared new lemmas. -/
run_cmd do
  let env ← Lean.getEnv
  let prefixes := ["Math.BoundaryProjectors.", "GUT.SU6BoundaryCube.",
    "GUT.SU6BoundarySelection.", "GUT.SU6BoundaryBaryon.",
    "GUT.SU6BoundaryInteractions.", "GUT.SU6BoundaryProtection.",
    "Physics.BaryonParitySelection."]
  let ds := env.constants.toList.filterMap fun (d, _) =>
    if prefixes.any (fun p => d.toString.startsWith p ||
        (d.toString.splitOn ("." ++ p)).length > 1) then some d else none
  let required := [``Math.BoundaryProjectors.Pair.range_joint,
    ``GUT.SU6BoundaryCube.contract_embed, ``GUT.SU6BoundaryCube.embed_covariant,
    ``GUT.SU6BoundarySelection.actual_left15_exact, ``GUT.SU6BoundarySelection.right20Equiv,
    ``GUT.SU6BoundaryBaryon.exterior_factor, ``GUT.SU6BoundaryBaryon.boundary20,
    ``GUT.SU6BoundaryBaryon.higgs_adjoint_fixed,
    ``GUT.SU6BoundaryInteractions.uv_20_15_invariant,
    ``GUT.SU6BoundaryInteractions.ir_15_20_invariant,
    ``GUT.SU6BoundaryInteractions.ir_6_15_invariant,
    ``GUT.SU6BoundaryInteractions.ir_1_6_invariant,
    ``GUT.SU6BoundaryInteractions.wrong_conjugation_not_invariant,
    ``GUT.SU6BoundaryProtection.all_degree_b1,
    ``GUT.SU6BoundaryProtection.neutral_control,
    ``Physics.BaryonParitySelection.derivative_selected_forbidden]
  for d in required do
    unless ds.contains d do throwError "boundary protection: required consumer {d} missing"
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "boundary protection: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Boundary protection: {ds.length} strict transitive checks passed"
