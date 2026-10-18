# Verification

## Foundation checkpoint

Commit `checkpoint 01` passed focused foundation builds, eight strict transitive
axiom checks, full `lake build` (5975 jobs), layout (922 modules), documentation
links and `git diff --check` at stage 01.

## Completion checks

The following checks are run on `proof/delta-l-two-weinberg` before the
completion commit:

```sh
lake build Math.RepresentationTheory.Audit.AuditMixedSquareDescent Physics.StandardModel.Operators.Audit.AuditWeinbergCompleteness
lake build
node tools/layout/check-layout.mjs
node tools/docs/check-links.mjs
git diff --check
```

Persistent strict transitive audits:

- [Mixed descent audit](../../../Math/RepresentationTheory/Audit/AuditMixedSquareDescent.lean):
  seven checks of descent, inverse and equivariant interfaces.
- [Foundation audit](../../../Physics/StandardModel/Operators/Audit/AuditWeinbergFoundations.lean):
  eight checks of mixed descent and normalized local invariant lines.
- [Completeness audit](../../../Physics/StandardModel/Operators/Audit/AuditWeinbergCompleteness.lean):
  27 checks covering residual and physical-sector equivalences, actual-field
  transport, nonzero criteria, one-generation controls, VEV evaluation and grading.

Allowed axioms are only `propext`, `Classical.choice` and `Quot.sound`.
No `sorry`, custom axioms, audit exceptions, dependency-pin changes or
increased heartbeat settings are introduced. Lean LSP was unavailable;
verification uses targeted Lean builds and the full build, not editor feedback.

Completion checks passed at stage 01:

- Focused audit build: 3727 jobs, including all seven descent and 27 completeness checks.
- Full `lake build`: 5984 jobs, including all three audit modules (42 checks).
- Layout: 931 modules; layers, imports, cycles, aggregates and relocation audits OK.
- Documentation: 344 Markdown files, 2105 local links, 33 heading fragments; zero errors.
- `git diff --check`: passed.

Existing dependency deprecation/style warnings were replayed. No warnings were
reported for the new Weinberg or mixed/exterior descent modules. Final review
checked the independently defined sector, both inverse identities, actual-field
input obligations and the distinction between nonzero coefficient and
nondegenerate mass. No physical matching premise is asserted as a theorem.

## Integration

The user explicitly authorized merging the existing interface unchanged.
`master` was still at the recorded base `checkpoint 02`, and the worktree was clean.
Topic commits `checkpoint 01` and `checkpoint 03` were merged with
`git merge --no-ff proof/delta-l-two-weinberg`; merge commit: `checkpoint 04`.

On the merged state, `lake build` passed (5984 jobs), including replayed
strict transitive audit results for all 42 declarations. Layout passed for
931 modules; documentation links passed for 344 Markdown files, 2105 links
and 33 fragments. Existing dependency warnings remain.

This integration-record update changes documentation only; links and
`git diff --check` were checked again, without an additional Lean build after
the prose-only edit. The topic branch is retained. No remote push was performed.
Input-interface unification is deferred, not part of the completed endpoint.
