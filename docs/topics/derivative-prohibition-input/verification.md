# Verification

## Proof Gates

```sh
LEAN_NUM_THREADS=2 lake build Math.RepresentationTheory.Audit.AuditDerivativeProhibition Physics.FieldTheory.Jets.Audit.AuditScalarProhibitionConditions Math.RepresentationTheory.Audit.AuditDerivativeInputAdapters Physics.FieldTheory.Jets.Audit.AuditInputAdapter
LEAN_NUM_THREADS=2 lake build
```

Both commands pass: 3877 focused jobs and 7703 full-build jobs. Execution
uses a 16 GiB inherited per-process address-space guard, two threads,
180/540-second focused/full wall-clock ceilings and default Lean
elaboration limits. No cap was raised. The full build is serialized after
the final focused proof/audit changes.

The persistent namespace-wide audits check all 112 new declarations,
including definitions, instances and generated helpers:

| Namespace | Transitive declaration checks |
| --- | --- |
| `Math.DerivativeProhibition` | 37 |
| `Math.DerivativeProhibitionControls` | 33 |
| `Math.DerivativeSelectionCounterexample` | 33 |
| `GUT.ScalarProhibitionConditions` | 9 |

Math rejects Physics/GUT imports and Physics rejects GUT imports. Every
owned declaration permits only `propext`, `Classical.choice` and `Quot.sound`
transitively. Each new namespace inventory must be nonempty. The preceding
Math/Physics adapter audits also pass their existing 125/32 checks.
All four new source modules and both audits are registered in the proper
aggregates; no audit allowlist is widened.

Final new sources have no warnings. Inherited dependency module-system
advisories remain. Intermediate proof elaboration/coercion mismatches and
local lint warnings were repaired before these gates. No mathematical or
resource stop was substituted for a proof.

## Assumptions And Compatibility Review

The [frozen contract](plan.md) and [results](results.md) agree. Scalar
detection is guarded by actual quotient support; the constituent converse
has explicit quotient semisimplicity. Target necessity retains actual
restriction surjectivity, with a proved counterexample when it fails.
Family predicates do not assert a nonlinear quotient decomposition.
The cubic parameter restriction is necessary for a nonzero global evaluation,
without a zero-coupling existence or whole-model prohibition claim.

Only aggregate imports change among pre-existing Lean sources. Published
nonderivative interfaces, derivative factories, dependency pins and existing
audit policies are unchanged. The source register and shared bibliography
agree on inherited roles; this is not another completed literature comparison.
The previous C1–C5 physical/completeness gaps remain explicit.

## Repository Gates

```sh
node tools/layout/check-layout.mjs
python3 tools/docs/check-topic-index.py
python3 tools/docs/check-work-metadata.py
node tools/docs/check-links.mjs
git diff --check
```

All final gates pass: 2209 modules with correct layer/import/aggregate
coverage; 159 indexed topics with 159 outcomes and no pending exception;
1199 portable documents/evidence files; 1207 Markdown files with 7659 local
inline links and 143 heading fragments, zero link errors; clean whitespace
checks. The local-link checker runs unchanged in a context permitting its
Git subprocess.

This implementation checkpoint was settled unmerged. A subsequent explicit
user request authorized integration; the [master integration record](master-integration.md)
contains the merged-state proof and documentation gates and supersedes that
earlier integration status. No remote update is authorized by either checkpoint.
