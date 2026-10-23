# Verification

## Preceding Integration

The helper is integrated into master, with preserved-history merge, focused
strict transitive audits, one serialized full build and safe local branch
retirement. The [integration record](../local-lagrangian-helper/master-integration.md)
owns that evidence: 572 declaration audits and 7691 full-build jobs pass.
This topic branches from the resulting master state.

## Planning Checkpoint

Six pinned primary sources have selected text and metadata inspection, with
locations, conditions and intended finite targets recorded. Murphy v6 and
Li v3 are used rather than carrying earlier-version page/formula assumptions
forward. Literal index transcription remains an execution gate. The plan
distinguishes relation certificates from basis/count certificates, free or
gaugeless specializations from full SMEFT, and each local stop from the
portfolio endpoint.

At that planning checkpoint all comparison rows were pending. No new Lean
result or build was registered for the documentation-only plan. The execution
checkpoint below supersedes that pending comparison state.

## Planning Documentation Gates

```sh
node tools/layout/check-layout.mjs
python3 tools/docs/check-topic-index.py --pending-topic derivative-literature-comparison
python3 tools/docs/check-work-metadata.py
node tools/docs/check-links.mjs
git diff --check
```

All gates pass: 2197 layout modules; 158 indexed topics with 157 outcomes
and the one explicit pending exception; 1186 portable documents/evidence
files; 1194 Markdown files with 7563 local inline links and 136 heading
fragments, zero link errors; `git diff --check` passes.

The pending exception applied to the planning checkpoint. Execution below
records the settled unmerged endpoint and uses the default topic check.


## Execution Proof Gates

```sh
LEAN_NUM_THREADS=2 lake build Math.RepresentationTheory.Audit.AuditDerivativeLiterature Physics.FieldTheory.Jets.Audit.AuditDerivativeLiterature
LEAN_NUM_THREADS=2 lake build
```

Focused builds pass 3308 jobs and 147 strict transitive declaration checks:
71 Math and 76 Physics, including definitions, instances and generated helpers
in all four new namespaces. Math rejects Physics/GUT imports; Physics rejects
GUT imports. Only the existing standard axioms `propext`, `Classical.choice`
and `Quot.sound` are permitted. All new source modules and both persistent
audits are registered in their aggregates.

The serialized full build passes 7697 jobs. Both gates use two threads,
a 16 GiB per-process address-space guard and default Lean limits. Focused
and full wall-clock guards remain 180/540 seconds. No guard or elaboration
limit was raised. There is no new-source warning in the final gates;
inherited dependency/module-system advisories remain. Intermediate local
proof elaboration and an untyped audit counter were repaired before the
successful gates; these were not recorded as mathematical/resource stops.

## Independent Exact Diagnostics

```sh
python3 tools/derivative-literature/check-one-dimensional.py
python3 tools/derivative-literature/check-scalar-lorentz.py
```

Both pass using only standard-library exact rational arithmetic. C1 checks
seven finite sectors, including the off-/on-shell quadratic control and
all six two-species targets. C2 checks all scalar jet monomials in the
1/20/305-dimensional sources and yields diagnostic dimensions (1,0,1).
The C2 command passes within its 180-second guarded invocation. Neither
script is a Lean premise; their unresolved semantic/group bridges remain
explicit in the results and coverage ledger.

## Final Scope And Documentation Review

All six queue rows are terminal: C1–C5 partial, C6 proved for its chosen
polynomial contract. No mismatch, resource stop or whole-paper validation
is asserted. Source interpretation, proof dossier, assumptions, bibliography
and coverage rows agree with the Lean statements. In particular, raw probes
are not quotient functionals, the component Higgs input has trivial action,
and the mixed current input does not impose Weyl EOM. The latter two have
no silently supplied physical dictionary or invariant completeness premise.

```sh
node tools/layout/check-layout.mjs
python3 tools/docs/check-topic-index.py
python3 tools/docs/check-work-metadata.py
node tools/docs/check-links.mjs
git diff --check
```

Final gates pass: 2203 layout modules; 158 indexed topics with 158 outcomes
and no pending exception; 1191 portable documents/evidence files; 1199
Markdown files with 7614 local inline links and 142 heading fragments,
zero link errors; `git diff --check` passes. Only aggregate
imports change among pre-existing Lean sources. The implementation, audits
and diagnostic scripts are additive. Public interfaces, dependency pins,
root README and existing audit allowlists remain unchanged. The topic has a
settled unmerged outcome-guide entry; its verified commit is not authorization
to merge into master or push remotely.

The separate user instruction subsequently authorized integration of the
present results. See [master integration](master-integration.md) for the
merged-state proof and documentation checks. This execution checkpoint's
earlier unmerged status does not describe the final integration outcome.
