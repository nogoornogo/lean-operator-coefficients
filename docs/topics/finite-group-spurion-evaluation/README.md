# Finite-Group Spurion Evaluation

- ID: `finite-group-spurion-evaluation`
- Status: completed
- Result type: proved finite-group evaluation, degree cutoff and coefficient consumer
- Working branch: `proof/finite-group-spurion-evaluation`
- Integration target: `master`
- Authorization: branch, planning, autonomous proof and same-branch degree extension
- Integration evidence: merged into `master` with `--no-ff` after explicit direction;
  merged-state verification passed; local topic branch deleted

## Endpoint And Scope

For a finite group H and finite-dimensional complex representations S and W,
prove that polynomial H-covariants S -> W evaluated at every specified s in S
surject onto the fixed space of the actual stabilizer H_s. Use the existing
coordinate-polynomial evaluation map, with finite coordinate sets I and J.
No genericity, faithful-action, or nonzero-value assumption is allowed.

The coefficient consumer takes W to be the contragredient of a supplied
finite-dimensional residual quotient Q_c and identifies W^{H_s} with
equivariant linear functionals Q_c -> C. Finite dimensionality is a hypothesis
of this consumer, not a new restriction on the general completeness theorem.

See the [frozen plan](plan.md) and [source register](references.md).
The general-group saturation stop in the
[predecessor](../all-degree-symmetry-protection/feasibility.md) remains intact.
No derivatives, IBP/EOM, algebraic geometry foundations, UV generation,
matching, rates, dependency changes or new model classification are included.

## Deliverables And Acceptance

1. Check the two named implementation routes in the plan; record exact APIs
   and unresolved prerequisites before implementing the proof package.
2. Prove finite-orbit interpolation and equivariant evaluation surjectivity,
   without a supplied spanning, interpolation or saturation premise.
3. Connect the fixed dual space to the existing residual-Hom coefficient
   interface, with the dual action and finite-coordinate transport explicit.
4. Register source and persistent strict transitive axiom audits in Math;
   run focused builds, layout checks and a serialized full `lake build`.
5. Document the proved statement, assumptions and limits; review local links
   and diff; commit coherent verified milestones on this branch.
6. Prove the authorized total-degree cutoff and bounded coefficient evaluation,
   with degree-zero/one controls and the same verification gates.

## Work And Open Obligations

The original endpoint and the authorized degree-bound extension are complete;
see [results](results.md). The degree proof stayed inside polynomial-degree
helper interfaces. No further proof work is required. General-group saturation,
minimal-degree classification and derivative topics remain outside scope.

## Result And Verification

`finite_group_surjective` proves surjectivity at every value.
`boundedEvaluation_surjective` proves the sufficient total spurion degree
`orbitSize a s - 1`, with uniform bound `Fintype.card H - 1`.
The bounded residual-Hom consumer recovers every coefficient within that cutoff;
finite-dimensional dual coordinates can be chosen by a basis.
The strict audits pass 29 original and 28 additional checks; the latest full
`lake build` passes 7460 jobs. See the
[dossier](../../proof/current/core/Math/FINITE_GROUP_SPURION_EVALUATION.md)
and [verification](verification.md). No operator mass-dimension bound or
paper-to-theorem equivalence is claimed. The topic is integrated into `master`.

The source register is reconciled with
[the literature list](../../proof/RELATED_LITERATURE.md). No coverage row is
warranted for this general result without a paper-to-theorem comparison.
The bibliography reconciliation and merged state were rechecked at integration.
The verified outcome is recorded in the [topic outcome guide](../_history/007_topics_history.md).
