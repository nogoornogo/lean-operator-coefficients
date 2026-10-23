# Structural Cubature Pilot Verification

This records the completed first-collinear pilot checkpoint. The resumed
[remaining-family verification](remaining-verification.md) owns the later
three-family state; the measurements and counts below retain their pilot scope.

The structural identity and its 140 unchanged family entry points pass focused
Lean builds. The dedicated strict audit checks 109 declarations, including
private helpers by defining module, against the original three standard axioms
and the Math layer boundary. The full build, exact type/reference checks and final constant-inventory
reconciliation pass.

## Measured Comparison

The same 35 first-collinear entry modules were compiled from source in separate
empty audit directories, together with their complete local dependency closures.
Neither run inherited ordinary project artifacts. Pinned external package and
toolchain artifacts were reused. One compiler ran at a time with `-j2`, a 16 GiB
virtual cap, a 540-second timeout and disabled core dumps.

| Measured scope | Before | After |
| --- | ---: | ---: |
| Local dependency closure | 47 modules | 52 modules |
| Fresh compiler invocations | 47 | 52 |
| Failed or reused project invocations | 0 | 0 |
| Total compiler time | 417.906 s | 174.705 s |
| Time for the 35 entry files | 326.802 s | 49.376 s |
| Maximum resident memory, whole closure | 3.72 GiB | 3.72 GiB |
| Maximum sampled virtual space, whole closure | 12.35 GiB | 11.28 GiB |

Including the five added structural dependencies, compiler time falls by 58.2%
in this run. Peak resident memory stays essentially unchanged; its maximum is
in the unchanged `Basic` data module. The new node certificates still use finite
kernel reduction. This is a structural proof and compilation-time improvement,
not a claim that all finite data checks or the data-loading peak disappeared.

The [summary](measurement-summary.json) and per-module
[before](before-measurements.csv)/[after](after-measurements.csv) CSVs retain
source hashes, measurements and run-specific dependency fingerprints. RSS is the
OS `wait4` maximum; virtual space is sampled Linux `VmPeak`, not physical RAM.
These are single-run repository-scale measurements, not universal bounds.

The comparison tool checks the exact selected closures, fresh events, frozen
before sources, source/setup/artifact hashes, actual imports and dependencies.
It repeats the profiler's current-fingerprint check on the candidate. The
full-project exporter and its complete-coverage requirement are unchanged.
An initial candidate preparation stopped before compilation because new modules
needed Lake setup files; these were created by the focused build. The subsequent
measured run compiled all 52 sources, with zero measured artifact reuse.

## Reproduction

For a new baseline, use the frozen pre-rewrite source checkpoint and an empty
`before` directory. For the candidate use another empty `after` directory.
The following shell form selects the same 35 targets for either run:

```bash
mapfile -t families < <(rg --files Math/Algebra/HiggsFourWaveCubature |
  rg '/R1M[0-9]+\.lean$' | sort)
args=()
for file in "${families[@]}"; do
  module="${file%.lean}"
  args+=(--only "${module//\//.}")
done
python3 tools/lean-memory/profile-project.py \
  --work-dir .lake/higgs-cubature-structure/after "${args[@]}"
python3 tools/lean-memory/compare-higgs-cubature.py \
  --before .lake/higgs-cubature-structure/before \
  --after .lake/higgs-cubature-structure/after \
  --output-dir docs/topics/higgs-cubature-structure
```

New modules need Lake setup files first. A normal focused build may create those;
the profiler excludes its local artifacts from the subsequent measured import
path. Logs, source/setup snapshots, type observations and compiled outputs remain
ignored build evidence. The tracked measurements contain no local paths or work
dates.

## Proof And Compatibility Gates

The [exact rewrite registry](proof-rewrites.json) records each original statement
and bounded before/after proof fragment, plus the import/docstring preamble.
The [source-addition manifest](source-additions.json) guards six new library files
and their explicit Math aggregate imports. Replay still checks all 4,218 older
source paths byte for byte after the reviewed transformations; original source
outside those fragments is unchanged. The other two moment families and all node
data remain unchanged. Generators reproduce 146 outputs from nine producers.

The original Higgs theorem hypotheses, dependency pins, axiom predicates and
allowlists are unchanged. No new literature premise or coverage claim is added;
the existing literature comparison remains a comparison to the same exact
formula. The bibliography therefore needs no new source entry.


The affected dependency chain was also built in order, one target per invocation:
60 stages passed without a timeout. The final ordinary `lake build` passes all
9,729 jobs. This ordinary incremental gate is separate from the serial measured
source compilations above; unrelated project sources and pinned packages may be
replayed. The first convenience focused build used ordinary Lake scheduling;
all resource comparisons use independent serial compiler invocations.

The 140 elaborated theorem types are exactly equal before and after the rewrite;
the [per-name type fingerprints](theorem-type-checks.json) retain that observation.
The public API check verifies 1,677 deprecated import facades and 12,989 aliases.
The reference check preserves occurrence order in 2,540 canonical modules outside
326 exactly registered proof fragments (186 parent and 140 pilot replacements).
Original statements remain inside the comparison. The Math namespace check covers
1,990 modules and the unchanged 4,227 historical correspondences.

New structural sources produce no warnings. Existing module-system import,
deprecation and retained-binder warnings are unchanged; no linter is disabled.


The complete constant export contains 74,756 repository constants. The original
foundation namespace count changes from 4,757 to 3,437: exactly 1,400 generated
finite-moment proof helpers disappear and 80 structural declarations/auxiliaries
are added. All old source-declared parents remain. The
[inventory record](audit-inventory-repairs.json) guards exact name-set hashes and
new source owners; the other nine messages in that audit are unchanged. Its Math
layer gate excludes six later Physics extensions of the same object namespace
from this count; those global-export names remain unchanged and are not skipped
by any Lean audit. All 422 prior audit-count records pass, with four unchanged
parent helper reconciliations and this separately identified source extension.
No strict axiom/import predicate or allowlist was edited.

Final repository checks pass: layout (4,232 modules), generators (nine producers,
146 exact outputs), source replay, API/reference checks, negative controls for
proof/preamble and inventory boundaries, profiler controls, documentation links,
topic navigation, portable metadata and `git diff --check`. Link checks report
zero errors. No new paper comparison is needed because the mathematical formula
and theorem premises are exactly preserved. The verified endpoint is committed
on its bounded child branch; neither parent nor master integration is implied.

Additional acceptance commands:

```bash
lake build Math.Algebra.HiggsFourWaveCubature.Structural.Audit \
  Math.Algebra.HiggsFourWaveCubature.Sorted1
lake build
HIGGS_CUBATURE_TYPE_EXPORT=/tmp/higgs-cubature-types.json \
  lake env lean -j2 tools/lean-memory/ExportHiggsCubatureTypes.lean
SOURCE_API_EXPORT=/tmp/higgs-cubature-constants.json \
  lake env lean -j2 tools/layout/ExportSourceAPI.lean
python3 tools/layout/check-audit-counts.py \
  /tmp/source-api-baseline-build.log .lake/higgs-cubature-structure/full-build.log \
  --baseline-constants /tmp/source-api-baseline-constants.json \
  --rebuilt-constants /tmp/higgs-cubature-constants.json
```

The baseline files in the final command are the frozen source-API observer
outputs documented in the [layout tool guide](../../../tools/layout/README.md).
They are disposable observations, not Lean premises. For serial incremental
reproduction, build the affected targets in dependency order before the final
`lake build`; all newly compiled dependencies then precede their consumers.
The explicit caps above apply to each invocation.
