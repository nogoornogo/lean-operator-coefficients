# Structural Conjugation Criterion

- ID: structural-conjugation
- Status: completed
- Result type: sufficient structural criterion proved, with actual positive and negative controls
- Working branch: `proof/structural-conjugation`
- Integration target: `master`
- Integration: completion gate passed; integrate into `master` with `--no-ff`, retaining the topic branch. Git ancestry records integration.

## Decision And Motivation

The user approved attempting the structural criterion after discussing its
possible overlap with established SU(5) arguments. Implementation was then
authorized following the plan commit `checkpoint 01`.

The group-free counterexample is complete. This topic restores explicit
geometric input: actual ambient elements implementing selected SM-weight
permutations while leaving residual charges unchanged. It does not retry the
refuted claim that the retained mass assumptions alone imply the obstruction.

This is a sufficient-condition theorem and proof-interface generalization.
Physical novelty, genuinely new model coverage, minimality and necessity are
not established. Merely removing the name SU(5) from hypotheses is not evidence
of any of them. Preserve existing proofs and the E6 literature boundary.

## Frozen Endpoint

For an arbitrary ambient group G with a supplied determinant-one rank-four
torus map, assume three actual conjugation identities implementing coordinate
swaps `(3 1)`, `(0 4)`, `(0 3)` (zero-based `Fin 5`). Retain an actual
finite-dimensional unitary representation of `G x H`, with H any Abelian
residual group, an invariant symmetric mass on the torus/H restriction, and
the specified positive finite-profile dual light target with singlets.

Derive the three charge-profile equalities, actual nonzero radical modes,
supported neutral `qque` and `duql` signatures, and failure of
`ForbidsEverySupportedPhysicalDeltaBOneOperator` on the actual resolved radical
spectrum. No full Weyl-invariance, profile-equality or support certificate is
an input. See the [precise interface and proof map](design.md).

The operator scope stays the existing dimension-six two-left/two-right class.
No nonzero Wilson coefficient, physical decay rate, full-gauge radical tensor,
quantum anomaly theorem or claim about all baryon-violating operators is added.

## Milestones And Progress

| ID | Deliverable / acceptance | State |
| --- | --- | --- |
| SC-0 | Freeze statement, inputs, reuse map, exclusions and stop gates | Completed; source interface type-checked |
| SC-1 | Actual three-conjugation interface; derive individual target invariances and charge-profile equalities without full Weyl invariance | Completed; [source checkpoint](source-checkpoint.md) |
| SC-2 | Connect invariant mass and exact dual target to actual radical coefficients, nonzero vectors and the supported-signature endpoint | Completed; [mass checkpoint](mass-checkpoint.md) |
| SC-3 | Construct conjugation witnesses for the existing SU(5)-to-G chain; compare actual spectra and preserve existing model/mass inputs | Completed; [adapter checkpoint](adapter-checkpoint.md) |
| SC-4 | Negative triality control, strict axiom/import audits, full regression, scope and added-generality assessment | Completed; [negative-control checkpoint](negative-checkpoint.md) |

Each milestone is a verified topic-branch commit, not permission to merge an
incomplete topic. Keep the overview short; put substantial proof results in
sibling checkpoint files instead of appending a session log.

## Routes And Stop Gates

The main route uses three separate coefficient-invariance lemmas and the
existing mass/spectrum APIs. A single fallback may extract the needed shared
parts of `TorusMassSource` into Physics, retaining old declarations as wrappers.
Neither route may import a SU(5) matter action into the general theorem or
replace the geometric input by the desired profile equalities.

Do not silently strengthen the mass to be G-invariant or assume its radical is
preserved by the conjugating elements. Move invariance through the source dual
index using the existing mass conservation theorem instead.

Stop and report if the fixed interfaces cannot deliver the endpoint without
changing hypotheses, a new theorem-level prerequisite outside the reuse map,
dependency upgrades, or new Lie/quantum-field foundations. Record the failed
obligation before requesting a scope change; do not recursively open helpers
as unbounded new tasks.

## Completion Gate

All SC-1 through SC-4 deliverables must pass. A conditional theorem remains
conditional on the three actual conjugations; their construction for arbitrary
G is not an obligation. SU(5)-chain witnesses are required as the positive
control, and the triality source is required as the negative control.

Document whether the change only reorganizes known cases or demonstrably
enlarges the applicability class. A new non-SU(5) physical model, classification
of all groups, or a necessary-and-sufficient criterion is a separate topic,
not a hidden completion condition. Then merge with `--no-ff` and retain the branch.

## Result And Remaining Boundaries

The [proved criterion](../../proof/current/inputs/Physics/STRUCTURAL_CONJUGATION.md) reaches the frozen
endpoint without strengthened mass invariance. The SU(5)-chain adapter uses
the same actual representation, mass and radical spectrum as existing models.
The actual 45-dimensional triality source cannot extend with matching restricted
character to data satisfying all three conjugations.

This generalizes the proof interface and recovers known chains; strictly wider
physical applicability has not been demonstrated. No obligation remains in
this bounded topic. New model coverage, necessity/minimality and amplitude
questions require separate approval and topics.

## Verification

SC-1 commit: `checkpoint 02` (10 strict checks); SC-2: `checkpoint 03` (11 checks).
SC-3: `checkpoint 04` (12 checks), including an actual 15-dimensional finite-residual
benchmark. SC-4 adds 7 checks, for 40 strict transitive axiom checks across the
four topic audits. Final `lake build` passed (5564 jobs); layout passed for 548
modules. Existing unused-section-variable warnings remain in
`Math/LinearAlgebra/FiniteBasisHilbertization.lean`; new modules emit no warnings.
Checkpoints record their own verification and scope.

Implementation gates: focused `lake build`, persistent strict transitive axiom
audits (only `propext`, `Classical.choice`, `Quot.sound`), complete `lake build`,
`node tools/layout/check-layout.mjs`, `node tools/docs/check-links.mjs`, and
`git diff --check`. General Physics modules must import no GUT application
modules. If Lean LSP MCP is unavailable, use source inspection and targeted
Lean checks; it was unavailable during planning and SC-1 implementation.

## References

- [Detailed design](design.md)
- [Assumption-sufficiency topic](../group-independent-assumptions/README.md)
- [Actual-source counterexample](../group-independent-assumptions/spectrum-bridge.md)
- [Existing standard-chain interfaces](../../proof/current/applications/GUT/interfaces/standard-su5-chain.md)
- [Shared selection rules](../../proof/current/applications/Physics/SHARED_SELECTION_RULES.md)
- [Dependency map](../proof-program-context/proof-dependencies.md)
