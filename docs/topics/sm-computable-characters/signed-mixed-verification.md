# Signed/mixed structural verification

Work follows `checkpoint 01` on `proof/sm-computable-characters` under the
[signed/mixed plan](signed-mixed-plan.md). See
[results](signed-mixed-results.md) and the
[general mixed stopping decision](signed-mixed-stop.md). No merge, push,
Lean/dependency pin change, root README edit or new literature premise occurred.

## Focused proof verification

All Lean commands used the existing persistent runner, `LEAN_NUM_THREADS=1`,
a 6 GiB sampled process-group stopping threshold and 4 GiB host reserve.
Builds and probes were serialized. The final source closure contains no
`sorry`, custom axiom, `native_decide`, `implemented_by` or `decide` in the
eight new proof modules. No exact multiplicity/rank computation or numerical
certificate was run. Generic arithmetic on degree, charge and admissibility
uses `omega`, proved formulae or finite species/Bool cases.

| Target | Result | Seconds | Sampled group peak KiB |
| --- | --- | ---: | ---: |
| Initial all-Q plus signed Q/L package | passed, `SMSignedHiggsSupport`, 4346 jobs | 9.3 | 5074316 |
| `MixedSupportSeparation`, final warning-free version | passed as mixed dependency | 6.3 for consumer | 5074352 for consumer |
| `PatternSpeciesRestriction` | passed | 4.5 | 4306092 |
| `SMChiralitySupport` | passed | 6.8 | 4994340 |
| `SMMixedConjugation` and final eight-family consumer | passed, 4352 jobs | 11.3 | 5074252 |
| `AuditSMStructuralSupport`, including admissible constant tests and mixed consumers | passed, 4357 jobs, 131 strict checks | 9.5 | 5375960 |
| `AuditStructuralExteriorSupport` | passed, 4024 jobs, 46 strict checks | 5.0 | 5175316 |
| `Math` aggregate | passed, 6016 jobs | 6.3 | 6194004 |
| `Physics` aggregate | passed, 5023 jobs | 5.3 | 5542440 |

The two strict audits total 177 checks and retain exactly `propext`,
`Classical.choice`, `Quot.sound`, layer boundaries and numerical-module import
rejection. Removed closed numerical modules remain archived, with active
symbolic evaluator audits preserved as recorded in
[retirement verification](retirement-verification.md).

Development corrected proof-only section variables, explicit involution
application, and elementary substitution. A concrete Q24/actual-field
intertwiner call exceeded default recursion depth; a generic-degree charge
restoration lemma resolved it. The first concrete mixed source transport
and a source scalar operator rewrite hit the default heartbeat limit. Moving
group/species restriction into the generic `PatternSpeciesRestriction` and
using pointwise tensor transport resolved them. No recursion/heartbeat or
proof-build stopping budget was raised. Final focused audits have no warnings
or errors. Chosen bases, source degrees and finite expansions remain symbolic.

## Aggregate resource boundary

The first post-retirement full default-library build stopped at 5.3 s,
sampled group RSS 6324252 KiB, above the same 6 GiB threshold. After all final
proof dependencies and Math/Physics aggregates passed, another guarded full
build of the default `GUT` library stopped at 5.5 s, 6424476 KiB. Neither
attempt ran a retired numerical proof; both reached the root aggregate load.

The final aggregate commands used runtime allocator purge settings to test
whether transient retention could be reduced, without changing Lean options,
proofs, trust or the resource guard:

```sh
MIMALLOC_PURGE_DELAY=0 MIMALLOC_ARENA_EAGER_COMMIT=0 LEAN_NUM_THREADS=1 \
  python3 tools/exact-rank/kernel-probe.py --build \
  --rss-limit-gib 6 --min-available-gib 4 GUT /tmp/signed-mixed-full-build.log
```

The Math/Physics aggregate measurements above use the same runtime settings;
focused proof measurements use the original environment. A final direct
`GUT.lean` check and no-build frontier are recorded below. Sampling can
overshoot the threshold and is not a hard memory limit. Full `lake build`
acceptance remains outstanding unless the final command explicitly succeeds;
focused theorem/audit verification is not reported as a successful full build.

## Repository verification

Eight new source modules are registered in the appropriate aggregate and
persistent strict audits. Layout passed for 1688 modules, including import
layers/cycles and aggregate coverage. The retirement checker still validates
19 snapshot hashes, 15 absent numerical modules and no active retired import.
Links, final cache/frontier, diff/assumption review and any residual warnings
are recorded below after the final pass.

The final direct `GUT.lean` check also stopped on the same group threshold,
at 3.5 s and 6338936 KiB. The final `lake --no-build build` returned 3 with
exactly `GUT` as the stale frontier (7056 graph jobs); no retired numerical
module remained. **Full default-build acceptance remains outstanding at the
root-aggregate resource boundary.** No stopping budget was raised and no
stopped check is counted as a proof. The final no-build checks of Math,
Physics and both structural audit roots passed with all targets up to date.

Final repository checks: layout 1688 modules; links 875 Markdown files,
5428 local links and 109 fragments, zero errors (read-only sandbox-subprocess
retry); retirement integrity 19 hashes/15 absent modules, passed; diff checks
passed. The final focused/aggregate success logs have no warnings or errors.
Lean/dependency pins, root README and CSV files are unchanged. No archived
numerical module was restored, imported, generated or executed.
