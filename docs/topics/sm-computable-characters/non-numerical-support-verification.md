# Non-numerical support verification

The [plan](non-numerical-support-plan.md) and
[result](non-numerical-support-results.md) distinguish the bounded original
Higgs-space iff from the still-open full signed Q/L constituent classification.
Work follows `checkpoint 01` on `proof/sm-computable-characters`; no merge or push,
Lean/dependency pin change, root README edit or new external premise occurred.

## Proof checks

Every Lean build used `LEAN_NUM_THREADS=1` and the persistent runner with
`--rss-limit-gib 6 --min-available-gib 4`. Builds were serialized. Typical
command (replace the module and temporary log path):

```sh
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build \
  --rss-limit-gib 6 --min-available-gib 4 \
  Physics.StandardModel.Operators.Audit.AuditSMStructuralSupport \
  /tmp/non-numeric-physics-audit.log
```

| Target | Result | Seconds | Sampled group peak KiB |
| --- | --- | ---: | ---: |
| `CompactCoefficientSupport` | passed | 4.8 | 4701176 |
| `SMGenerationCoefficients` | passed | 8.3 | 5086104 |
| `SMLowerGenerationSupport`, before vacuum extension | passed | 5.0 | 5048704 |
| `AuditSMStructuralSupport`, including final vacuum and all-count L/Q-lower Higgs consumers | passed, 4347 jobs, 78 strict checks | 8.8 | 5358532 |
| `AuditStructuralExteriorSupport` | passed, 4011 jobs, 42 strict checks | 4.8 | 5171812 |
| `Math` aggregate | passed, 6014 jobs | 5.5 | 6266164 |

Both strict audits retain only `propext`, `Classical.choice`, `Quot.sound`,
layer checks and numerical-evaluator/certificate import rejection. No policy
or allowlist was relaxed. All four new sources contain no `sorry`, custom
axiom, `native_decide`, `implemented_by` or `decide`. The final two focused
audit roots were also checked together with `lake --no-build build`; their
entire dependency graph was up to date and the command passed.

Development corrected API qualification, explicit Borel measurable instances
on the compact semisimple group, and elementary arithmetic. A whole-carrier
identity equivalence in `actionEquiv` exceeded the default heartbeat limit;
the retained proof uses explicit tensor-factor linear equivalences and
operator intertwining. No heartbeat/memory budget was increased. The final
focused builds above have no warnings or errors. Resource measurements are
sampled observations of these runs, not a space-complexity guarantee.

No closed character, exterior-basis, multiplicity or constraint-matrix
calculation was run. Small arithmetic concerning degree/parity/admissibility
uses general symbolic lemmas and `omega`; it does not evaluate the numerical
rank classifier. Existing exact numerical example statements were preserved.

## Whole-project build boundary

An initial `lake --no-build build` returned 3, listing the changed `Math`
aggregate and the two retained numerical example modules as stale frontier.
After the guarded Math aggregate build passed, the final no-build check
returned 3 with exactly these two stale frontier modules:

- `Physics.StandardModel.Operators.SMComputableCharacterExamples`
- `Physics.StandardModel.Operators.SMNeutralSparseExamples`

The required guarded full-build attempt used:

```sh
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build \
  --rss-limit-gib 6 --min-available-gib 4 \
  --require-cached Physics.StandardModel.Operators.SMComputableCharacterExamples \
  --require-cached Physics.StandardModel.Operators.SMNeutralSparseExamples \
  GUT /tmp/non-numeric-full-guard.log
```

It refused to launch at the first cache prerequisite (exit 3 from the
no-build preflight). `GUT` is the repository's default `lake build` library.
No legacy numerical reduction was launched or rerun. The previous numerical
resource stops remain recorded in [Q18 verification](q18-support-verification.md).
**Full-project build acceptance remains outstanding.** The new theorem closure
and strict audits passed independently; this record does not claim a new
successful full-project baseline.

## Repository checks

Four new sources are registered in `Math.lean` / `Physics.lean`; the existing
structural audits include their generic connections and actual final consumers.
Layout passed for 1682 modules, including aggregate coverage and layer/cycle
checks. `node tools/docs/check-links.mjs` passed for 869 Markdown files, 5381
local links and 109 fragments with zero errors, using the same read-only
command outside the sandbox after its `git ls-files` subprocess hit EPERM.
`git diff --check` passed. No CSV cell or old numerical theorem statement was
changed. Final focused cache verification passed for both audit roots
(4348 jobs, all up to date).
