# Proof Memory Audit Verification

At the proof-memory acceptance, all 4,226 registered project modules had a
measured successful compilation of their then-current source/dependency
fingerprint. The final independent fingerprint,
artifact, log and actual-import check passes; no failed, blocked or unresolved
review-threshold module remains. The ordinary full build and public API/reference
comparisons also pass at that checkpoint. The later
[master integration](../source-api-compatibility/master-integration.md) includes
this child through its recorded parent, with separate merged-state checks.
Later cubature changes and model additions do not inherit this earlier
fresh-compilation coverage claim.

## Measurement Scope

Each module ran in a separate pinned Lean 4.35.0 process, one at a time, with
`-j2`, a 16 GiB virtual-address-space limit, a 540-second timeout and core dumps
disabled. Local sources and setup data were snapshotted; ordinary project build
outputs were excluded from import resolution. All local dependencies came from
this measured build. External package/toolchain artifacts remained pinned reusable
inputs. Resumes explicitly reused only this audit's verified measured artifacts;
they did not count inherited project caches as source compilation.

- [Per-module measurements](module-measurements.csv): source hashes, closure
  fingerprints, compiler exits, times, resident/virtual peaks and thread counts.
- [Protocol and maxima](measurement-summary.json): 4,226 successes; maximum
  resident memory 5.92 GiB (`GUT`), maximum sampled virtual memory 13.96 GiB
  (`Math.LieGroups.E6.Minuscule.CubicTorusReconstruction`), longest invocation
  282.5 seconds. The `GUT` aggregate consists of imports, so its peak concerns
  loading the complete environment.
- [Hotspot comparisons](hotspot-measurements.json): original, optimized and
  matching import-only measurements for all 12 changed modules.

Resident peaks use OS `wait4` maximum-RSS accounting. Virtual peaks sample Linux
`VmPeak`; virtual address space is not physical RAM consumption. Fingerprints
include run-specific relocated setup paths and do not promise cross-checkout
artifact identity. Full logs, source/setup snapshots and build artifacts remain
ignored under `.lake/proof-memory-audit/`.

## Proof Improvements

Five modules replace expensive proof work while preserving statements,
hypotheses, supplied tables, resource limits and strict axiom allowlists.

| Source / change | Before resident / virtual | After resident / virtual |
| --- | --- | --- |
| [SixSlotRestrictionLift](../../../Math/RepresentationTheory/Tensors/SixSlotRestrictionLift.lean): reflexivity replaces two expanded bundled-map proofs | 6.50 / 12.10 GiB | 3.40 / 9.17 GiB |
| [SixColorInvariant](../../../Physics/StandardModel/Gauge/Tensors/SixColorInvariant.lean): reuse trilinearity instead of expanding determinants | 4.32 / 14.37 GiB | 4.01 / 13.34 GiB |
| [E6 LieCertificateChecks](../../../Math/LieGroups/E6/Minuscule/LieCertificateChecks.lean): split six kernel decisions by their first finite index | 6.36 / 12.30 GiB | 3.76 / 9.36 GiB |
| [LiSixQuarkYoungImages](../../../Physics/StandardModel/Operators/BaryonTwo/Li/LiSixQuarkYoungImages.lean): normalize scalar zeros/cancellation after coordinate expansion, before ring reflection | 6.41 / 12.26 GiB | 5.23 / 11.26 GiB |
| [E6 SU5LieImage](../../../GUT/E6/Minuscule/SU5LieImage.lean): split the 25 finite matrix cases before kernel decisions | 8.19 / 14.13 GiB | 5.01 / 11.13 GiB |

The Lie-certificate comparison uses two completed sequential runs; its original
asynchronous run failed to create a worker thread at 15.49 GiB virtual memory.
The finite decisions still use `decide +kernel`. Splitting the Lie checks trades
some time for memory: 69.2 to 93.9 seconds. Restriction proofs improve from
92.5 to 11.6 seconds; Young-image proofs improve from 137.9 to 112.8 seconds.

The [exact replay registry](proof-rewrites.json) contains 186 declaration-bounded
proof-body replacements. Every original statement and every resolved reference
outside those exact bodies remains a comparison boundary. For the Young-image
module, the [type observer](../../../tools/lean-memory/ExportYoungImageTypes.lean)
compares all 196 source-declared public/private types before and after the change;
its byte-identical inventories have SHA-256
`fd5534e92843ef471132b82c493b7cb5b1125deebee7ebc257c64f03e3a7f2cb`.

Matching import-only resident/virtual controls are 3.28/8.09 GiB (restriction),
3.32/8.14 GiB (color), 3.40/8.28 GiB (Lie certificates), 3.38/8.24 GiB
(Young images) and 4.13/9.11 GiB (E6 SU(5) image). These controls omit the
target proof body and do not count as its successful compilation.

The earlier [15.98 GiB Fierz comparison](../source-api-compatibility/resource-investigation.md)
concerned unrepaired sources. The parent's coordinate-based repair was measured
without further changes at 3.39 GiB resident / 9.33 GiB virtual, in 2.0 seconds.

## Scheduling Repairs

Eight exact module-local `Elab.async false` insertions reduce observed worker
counts and associated virtual reservations without changing resource limits. Seven modules below retain every
proof body. The eighth is the E6 Lie-certificate module above, which also receives
finite-case proof splits. Observed OS-thread peaks fall from 10–12 to five.
These address scheduling and virtual reservation, separately from proof heap use.

| Source | Before resident / virtual | After resident / virtual | Import-only resident / virtual |
| --- | --- | --- | --- |
| [SixSlotSpeciesSum](../../../Math/RepresentationTheory/Content/SixSlotSpeciesSum.lean) | 3.67 / 15.29 GiB | 3.62 / 9.17 GiB | 3.27 / 8.09 GiB |
| [E6 D5Blocks](../../../Math/LieGroups/E6/Minuscule/D5Blocks.lean) | 2.97 / 15.95 GiB; thread-creation failure | 3.09 / 8.83 GiB; success | 2.94 / 7.75 GiB |
| [E6 MatrixLieBasis](../../../Math/LieGroups/E6/Minuscule/MatrixLieBasis.lean) | 4.60 / 15.49 GiB | 4.59 / 10.30 GiB | 3.40 / 8.29 GiB |
| [FlavoredCyclicControls](../../../Physics/StandardModel/Operators/Selection/FlavoredCyclicControls.lean) | 3.85 / 15.88 GiB | 3.83 / 9.76 GiB | 3.77 / 8.68 GiB |
| [HiggsQuarticFourInternalUpper](../../../Physics/FieldTheory/Jets/Higgs/QuarticFour/HiggsQuarticFourInternalUpper.lean) | 3.73 / 14.70 GiB | 3.70 / 9.58 GiB | 3.65 / 8.50 GiB |
| [SU5 InvariantMassNormalForm](../../../GUT/SU5/SelectionRules/InvariantMassNormalForm.lean) | 3.86 / 15.83 GiB | 3.84 / 9.70 GiB | 3.78 / 8.63 GiB |
| [SU5 ActualHyperchargeProfiles](../../../GUT/SU5/Branching/ActualHyperchargeProfiles.lean) | 4.04 / 15.84 GiB | 4.02 / 9.72 GiB | 3.79 / 9.72 GiB |

A failed run's smaller resident peak is not a completed-proof memory improvement.
The original focused strict audits pass: restriction 7, color 13, species 12,
E6 compact 38, matrix Lie 37, Geck comparison 41, Young source derivation 15,
flavored selection 55, Higgs 16 namespace inventories plus the layer check,
E6 SU(5) inclusion 31, SU(5) mass 52 and actual full family 38 checks.

## Acceptance Gates

| Gate | Current result |
| --- | --- |
| Isolated whole-project source compilation and `--resume --check` | 4,226 successful current fingerprints; zero failures, blocked modules or unresolved review thresholds |
| Profiler/registry controls | 11 pass; actual fresh/reuse/tamper-rejection/recovery and boundary-pause controls pass |
| Exact audit-message controls | Four tests pass, including rejection of any change to adjacent count messages |
| Ordinary complete `lake build` | Pass, 9,723 jobs; four bounded warm-up timeouts followed by a successful fifth run |
| Public API and references | 1,677 deprecated imports, 12,989 protected aliases and 2,540 canonical reference/occurrence sequences pass; 186 exact proof fragments and 16 recorded scheduling references are accounted for |
| Math namespace inventory | 1,984 modules and 4,227 historical correspondences pass; no legacy Math-owned declarations |
| Complete constant/audit-count reconciliation | 76,048 rebuilt repository constants exported; 422 audit-count records match with four exact helper reconciliations (three from the parent, one from this child) |
| Source replay, layout and generator controls | Frozen-source replay and 4,226-module layout pass; eight generators reproduce 144 outputs exactly |
| Migration/layout regressions | Three migration tests and the layout regression suite pass |
| Documentation and final diff | Local links, topic outcomes, portable metadata and whitespace checks pass |

The ordinary rebuild completed 141, 140, 144 and 325 fresh Lake tasks before
its four 540-second warm-up limits. The fifth run completed the remaining 19
tasks and the whole default target. No proof error occurred and no limit was
increased. This ordinary incremental sequence is separate from the complete
measured source-compilation gate.

The profiler rejects inherited project artifact paths, stale dependencies, changed
artifacts, wrong actual project imports, logged compiler errors and timeouts even
when the terminated compiler exits zero. Source replay rejects unregistered
statement/proof changes. Strict audit predicates and axiom allowlists are unchanged.
The [Higgs helper inventory](audit-inventory-repairs.json) changes from 305 to
285 under sequential elaboration: 45 old helper names are replaced by 25 shared
or renumbered helpers, all under five retained source-declared parents. Complete
constant inventories verify the exact removed/added name hashes and helper-only
categories. Only the fifth of 16 audit-count messages changes; all remaining
messages and protected parents are preserved. The three prior parent-topic
reconciliations also remain exact; no audit predicate or allowlist is relaxed.

The simpler Young-image proofs leave 94 unused-section-variable warnings for the
original `[CharZero K]` hypothesis. Keeping that common binder preserves all
existing types; no linter or axiom/import audit is disabled. Existing deprecation
and legacy/module-system import warnings remain outside this proof-memory scope.
The documentation metadata registry recognizes the pinned binary's upstream Lean
4.35.0 revision as external source metadata; no local work-history exemption or
dependency-pin change is introduced.

No fresh external-dependency rebuild or universal compiler-memory bound is claimed.
The review thresholds are 6 GiB resident or 14 GiB virtual memory per measured
process. Ordinary incremental build success is recorded separately from actual
source-compilation coverage.

## Reproduction And Recorded Commands

Use the [fresh-run commands](README.md#profiler) from the topic overview. The
portable exporter repeats the complete current-fingerprint check before writing
measurements. A new empty audit directory compiles every source again; a resume
reports verified reuse separately.

The acceptance sequence additionally used ordinary `lake build`,
`check-source-api.py`, `check-math-namespaces.mjs`,
`check-source-references.py /tmp/source-api-baseline-metadata.json`, source replay,
layout/generator regressions, the complete constant exporter and
`check-audit-counts.py` with both exported inventories and the successful build
log. Their [tool guide](../../../tools/layout/README.md) explains the frozen
baseline inputs and exact comparison boundaries. Baseline/full logs remain
disposable build evidence, separate from the portable measurements retained here.
