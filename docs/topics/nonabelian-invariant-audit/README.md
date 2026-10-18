# Non-Abelian Invariant Audit

- ID: nonabelian-invariant-audit
- Status: completed
- Checkpoint detail: completed (bounded feasibility audit, not the non-Abelian no-go)
- Working branch: `proof/nonabelian-invariant-audit`
- Integration target: `master`; integrate after the final verification gate
- Result type: checked algebraic lemmas and a scoped positive feasibility decision

## Frozen Endpoint

Assess extension of the structural conjugation criterion from Abelian residual
symmetries to finite ordinary non-Abelian residual symmetries. Keep the actual
three ambient conjugations, finite-dimensional complex matter, commuting UV
and residual actions, restricted unitarity, and invariant symmetric mass.
Do not assume that conjugation preserves the radical. The replacement for
charge-resolved positive light profiles must retain residual representation
information, not just dimensions. Deriving that replacement is an open bridge,
not an already accepted new physical premise.

The algebraic endpoint is a nonzero invariant ordered four-factor coefficient
functional with the dual factors appropriate to qque/duql. This is not yet
a nonzero operator after Lorentz/Grassmann relations, a Wilson coefficient,
an amplitude, or a proton-lifetime theorem. Do not equate these endpoints.

## Bounded Milestones

| ID | Deliverable | State |
| --- | --- | --- |
| NA-1 | General evaluation pairings: actual equivariance and nonzero four-factor functional | Proved; checkpoint verification below |
| NA-2 | Exact controls for S3 and A4, initially multiplicity dimension at most 3; state coverage and dual conventions | Proved for two named sum-zero representations and matched/unmatched patterns |
| NA-3 | Audit the light-spectrum bridge against existing conjugation and mass-index APIs; report closed/open inputs | Audit complete; positive-character quotient and nonzero pullback proved; actual weightwise source bridge open |

Two routes only: canonical evaluation pairings, and exact finite-group
representation checks. Examples test the interface, not prove universality.
An assignment of independent SM flavor representations is not a counterexample
unless all retained UV, mass and target conditions are verified. Conversely,
absence of a counterexample is not a theorem. Do not implement SU(2)/SU(3)
flavor classification, new Lie foundations, or non-SU5 embeddings in this task.

## Stop Gate

Stop after the two named finite groups and a concrete bridge assessment:
an assumption-respecting counterexample, a bounded general proof route with
explicit remaining inputs, or a documented failed implication are all valid
audit outcomes. Further foundations or stronger physical endpoints require
approval. Preserve every existing Abelian theorem and the E6 literature boundary.

## Starting Evidence And Next Action

- `SymmetricMass.radical_dual_character_eq` already works for arbitrary groups.
- The existing scalar-charge spectrum uses `CommGroup`; it cannot be reused
  unchanged as a non-Abelian representation-valued index.
- General multiplicity/commutant infrastructure already accepts non-Abelian groups.
- NA-1 constructs a nonzero coefficient on `(V tensor V*) tensor (W tensor W*)`
  for any group and nonzero vector spaces. It is a functional, not an element
  of the same tensor space. Dual-factor order is explicit.
- The radical dual-character difference is invariant under actual ambient
  conjugation for arbitrary residual groups; no radical-preserving action of
  the conjugator is assumed. This closes only the trace stage of NA-3.
- S3 (dimension 2) and A4 (dimension 3) have checked positive paired controls
  and negative unmatched four-factor controls. See [coverage](finite-controls.md).
- Positive character content now yields actual irreducible quotients for
  finite residual groups. Matched quotient maps preserve a nonzero coefficient.
- The [bridge assessment](bridge-assessment.md) records the remaining actual
  weightwise source construction, local-target contract and physical ordering.
- Stop at this audit endpoint. A separate source-bridge task requires approval;
  no non-Abelian physical no-go or complete counterexample search is claimed.

See [the initial checkpoint](initial-checkpoint.md) for declarations and the
remaining gap between character identities and actual light invariant tensors.

## Verification

Focused build of the two persistent audits: passed, 2343 jobs, eight strict
transitive axiom checks (only `propext`, `Classical.choice`, `Quot.sound`).
Full `lake build`: passed, 5578 jobs. Existing deprecated-import and linter
warnings were replayed; the new modules produced no warnings. Layout: passed,
562 modules. Documentation: 234 Markdown files, 1255 local links, 32 fragments,
zero errors. `git diff --check`: passed. These are the NA-1 checkpoint counts.
No dependency pins or existing Abelian statements changed.

NA-2 focused build: passed, 3081 jobs, 13 additional strict axiom checks.
Full regression: passed, 5585 jobs (existing warnings replayed; new modules clean).
Layout: passed, 564 modules. Links: 235 Markdown files, 1258 local links,
32 fragments, zero errors. Staged diff whitespace check passed.

NA-3 focused audits: passed, 2327 jobs, eight additional strict checks.
Across the topic: 29 new strict transitive axiom checks. Final `lake build`:
passed, 5589 jobs, with existing warnings replayed and new modules clean.
Layout: 568 modules passed. Links: 236 Markdown files, 1263 local links,
32 fragments, zero errors. Staged diff whitespace check passed.
The bounded audit completion gate is satisfied; integration evidence is Git
ancestry. No complete non-Abelian physical theorem is implied by this gate.

Lean LSP MCP is unavailable in this session. Use source inspection, focused
Lean builds, strict transitive axiom checks, full `lake build`, layout/link
checks and `git diff --check`. Commit verified milestones; retain the branch.

## References

- [Structural criterion](../../proof/current/inputs/Physics/STRUCTURAL_CONJUGATION.md)
- [Current partial target](../conjugation-partial-target/README.md)
- [Mass dual index](../../../Physics/FieldTheory/Mass/SymmetricMassIndex.lean)
- [Multiplicity centralizer](../../proof/current/inputs/Math/MULTIPLICITY_CENTRALIZER.md)
