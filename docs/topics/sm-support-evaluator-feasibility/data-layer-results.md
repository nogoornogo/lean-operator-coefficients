# Executable data-layer result and resource stop

The [subsequent connection revision](data-connection-results.md) closes the SM
bridge boundary. This record retains the earlier partial-result checkpoint.

## Status and scope

The [authorized plan](data-layer-plan.md) was followed through the mathematical
core data and generic generation/species composition. The full SM bridge build
hit the frozen 10 GiB sampled process-group RSS guard. Development stopped at
that gate; the SM bridge and individual mixed support consumers are **not
verified**. No larger memory/proof budget or alternative search algorithm was
used. Subsequent work only audits, builds and records the retained verified
partial result.

## Retained mathematical result

- [JointSourceData](../../../Math/RepresentationTheory/JointSourceData.lean)
  defines executable color/weak/spin atoms, scalar, single-spin and paired-spin
  exterior syntax, uniformly in degree and independent spin placement.
  `single_eq` and `doubletPair_eq` identify the syntax with the existing
  actual presentations, including vacuum and overflow.
- [ColoredSourceData](../../../Math/RepresentationTheory/ColoredSourceData.lean)
  defines executable color duality, color/single-spin and Q-core expressions.
  `colored_eq`, `conjugateColored_eq`, `quark_eq`, and `conjugateQuark_eq`
  prove uniform correspondence to their actual mathematical presentations.
  Complementary degrees, duplicate summands and tensor association are retained.
  The functions cover all mathematical core families needed by the signed SM
  dictionary; the ten-species Physics dispatch is not claimed as checked.
- [JointContentData](../../../Math/RepresentationTheory/JointContentData.lean)
  composes numeric occupations and species without runtime representation data.
  `choiceEquiv` identifies compact indices with old generation choices;
  `generations_eq` and `occupied_eq` prove expression correspondence by ordinary
  rewriting and induction for any indexed dictionary of the existing group.

Every new semantic proof uses ordinary structural cases, rewriting, constructor
reduction or induction. No `decide` variant, native computation proof,
`omega`/`norm_num`, Boolean reflection or imported numerical certificate closes
any new proof. Existing compact occupation equivalences and mathematical
presentations are reused; this restriction does not rewrite their earlier
proofs. Definitions compute syntax, not ranks or a support verdict. The 56
new named declarations have a persistent strict transitive axiom audit.

## Where the stop occurred

The unverified
[SM candidate](../../../tools/structural-support/probes/sm-joint-support-data-candidate.lean.txt)
proposes `coreData_eq`, `expressionData_eq`, `dataSupport_iff`,
`higgsDataSupport_iff` and an original-space corollary. Its complete focused
build was interrupted at **60.1 s**, sampled group peak **10508652 KiB**
(about **10.02 GiB**). This slight overshoot is a sampling effect; the configured
guard remained 10 GiB with 4 GiB host reserve. Child exit was -2. The log had
no completed-declaration diagnostics, so the run does not identify which
particular declaration caused growth. Do not infer a specific bottleneck,
compiler-optimization defect or mathematical obstruction from this evidence.

The candidate is kept only as `.lean.txt` outside active source roots. It is
not imported by Math/Physics/GUT aggregates, audited as a result or counted as
a theorem. No active `SMJointSupportData.lean` module is retained.
The remaining gate is a checked ten-species dispatch/composition correspondence
and its support/Higgs/original-space transport under the existing resource
budget. The planned ordinary mixed positive and negative consumers depend on
that gate and were not attempted. Resuming diagnosis or changing the budget
requires a new user decision; no retry follows this stop automatically.

## Verification record

All commands use `LEAN_NUM_THREADS=1`, no proof-option/pin changes, one Lean
run at a time, 300 seconds per guarded run, 10 GiB RSS and 4 GiB host reserve.
Guarded focused checks use:

```text
python3 tools/exact-rank/kernel-probe.py --build MODULE /tmp/LOG --rss-limit-gib 10 --min-available-gib 4
```

| Check | Result | Seconds | Sampled peak KiB |
| --- | --- | ---: | ---: |
| Initial single/paired-spin data build | pass | 8.5 | 4899000 |
| Final colored/Q data focused build | pass | 5.3 | 4985464 |
| Generic composition focused build | pass | 4.8 | 4947216 |
| Retained modules plus strict audit build | pass, 56 strict checks | 14.0 | 5295848 |
| Full SM bridge candidate | interrupted at RSS guard | 60.1 | 10508652 |

Two early monolithic Q correspondence attempts hit the unchanged default
200000-heartbeat limit (10.0 s/4983908 KiB and 9.8 s/4984728 KiB). Splitting
ordinary complementary-degree lemmas and reusing them resolved that elaboration
issue without raising limits. These failed attempts are not accepted proofs.
Runtime smoke diagnostics initially required an explicit `IO Unit` annotation;
that harness type error was corrected without changing data/proof definitions.

Final partial-result verification:

| Check | Result | Seconds | Sampled peak KiB |
| --- | --- | ---: | ---: |
| Runtime degree 6 | data-only output; Q/conjugate-Q 20, two-species 400 | 3.3 | 4874852 |
| Runtime degree 13 | all listed core/composition outputs zero | 3.5 | 4884444 |
| Direct strict audit source rerun | 56 strict transitive checks | 3.8 | 5229344 |
| Full default-root `lake build GUT` | 7329 jobs; zero warnings/errors | 16.5 | 6695132 |

The full-build peak is about 6.39 GiB. It verifies only the retained active
library, which excludes the stopped SM candidate. Runtime inputs come from
`SM_DATA_DEGREE`, so these diagnostics compile the parameterized functions,
not separately extracted closed presentations. The
[smoke template](../../../tools/structural-support/probes/joint-source-data-smoke.lean.txt)
and [commands](../../../tools/structural-support/README.md#executable-source-data-diagnostics-and-stopped-sm-bridge)
are retained. Output values are not support proofs.

Layout: 1943 modules, all layer/import/aggregate checks pass. Local links and
diff checks pass. New proof-source policy inspection confirms no prohibited
computational proof tactic or raised option. The new axiom audit is rerun
directly, not merely inferred from a cached full build. The
[machine-readable record](../../../tools/structural-support/results/data-layer-summary.json)
preserves measurements, scope and accepted/unverified source hashes.
No merge, push or branch deletion was performed. This completes verification
of the retained partial result; the implementation endpoint remains stopped.
