# Initial frozen plan (stage 01)

This plan is fixed before implementation on `proof/sm-finite-charge-support`,
based on `checkpoint 01`. Integration target is
master; no merge/publication/push is authorized. It implements the user's
approved two-stage review response. A bounded child branch may be used for
stage 2 and merged only into this unmerged parent under the workflow exception;
it must have its own topic record if used.

## Stage 1: maintained verification and interpretation

1. Add a named opt-in command which regenerates the 572 proof certificate and
   CSV, compares the retained table and source identity, kernel-checks all
   proofs with the existing strict transitive audit, and records measurements.
   Generated files/logs stay in a fresh explicit temporary directory. The
   default library build is not represented as checking this target. Build
   required imports before the fresh certificate. A failing comparison or
   missing final audit fails the command. Never refresh expected hashes or
   verdicts automatically after a failure.
2. Prove for every ordered signed pattern the arithmetic lower bound
   `|B3| + |L| ≤ n`, where B3 is integer three-baryon charge and n is fermion
   degree. Derive `3 + |L| ≤ n` for B1 and `6 + |L| ≤ n` for B2.
   Use twice the engineering dimension `3*n + 2*(h+d)` to avoid requiring
   rational-valued infrastructure. This quantity is a grading convention,
   not a claim about an anomalous dimension or a decay rate.
3. Check and record the full |L| distributions and the 278 B1 assignments
   excluding |L|=1. Prefer kernel certificates for the closed charge gates,
   connected to the generic support/parity/degree lemmas. Explain the
   resulting n≥6, engineering dimension≥9 lower bound without claiming a
   minimum or that the selected witness minimizes total dimension.

## Stage 2: finite attainable charges

The desired criterion is, for b=3 or 6, actual all-degree original allowance
iff there is an attainable L with b*q+L*l=0. Define attainable charges using
actual neutral-residual support at B3=b, not by congruence solvability.
Prove the sign/conjugation bridge needed to cover the absolute-B3 selector;
do not silently replace absolute B3 by positive B3.

Required interfaces and routes:

- Capacity and parity: derive |L|≤18 and even B3+L for nonzero support;
  hence B1 candidates ±1,±3,…,±17 and B2 candidates 0,±2,…,±18.
- Positive route: reuse the existing full joint occupation/component witness
  bridge and 23 checked families. Inspect explicit bounded variants for
  remaining candidates, allowing additional quark/antiquark pairs. No
  unbounded dressing induction and no factorwise substitute for joint support.
- Negative route: use existing capacity, hypercharge, weak/chirality and
  Higgs admissibility filters to exclude unattainable candidates for all
  contents/Higgs bidegrees. Missing witnesses do not count as exclusions.
- Once every candidate is resolved, define concrete finite sets R1/R2,
  prove the original-space equivalence for arbitrary k,q,l, register/audit
  it in Physics, and recover all 572 assignments as corollaries. Compare
  the recovered table to the existing certificates before replacing them.

The feasibility investigation is one pass through these two routes. Do not
start foundational duality/representation theory, a general compiled solver,
or a large exhaustive content search to force closure. If necessary, retain
proved outer/inner finite bounds and identify unresolved L and exact missing
interfaces. Defining a semantic finite set alone is not determination of R.

## Resources, verification and stop conditions

One Lean process/build at a time, one Lean thread, unchanged pins/options,
300 seconds per probe/build, 10 GiB sampled process-group RSS and 4 GiB host
reserve. Use the retained guarded runner; report overshoot and interruptions.
Do not repeat the old raw evaluator or expensive projection diagnostics.

At verified source milestones: focused builds, persistent strict transitive
audits allowing only propext/Classical.choice/Quot.sound, serialized full
`lake build GUT` (the default root), layout, links and diff checks. Update
the Physics assumptions ledger and relevant proof dossier with proved scope.
No sorry, custom axioms, native_decide, audit exceptions or raised limits.
Ordinary algebra/count proofs are preferred; existing kernel-checked finite
certificates remain an allowed route for closed support witnesses.

Stop before new physical scope, dependencies, foundational prerequisites or
resource-limit increases. Minimum engineering dimension is a separate future
optimization, not an obligation here. Preserve unrelated work and commit
verified coherent milestones; continue toward the endpoint after checkpoints.
