# Structural support feasibility probes

## Bounded weak-connection localization

`b1-weak-localize.py counts --progress /tmp/NEW-count-progress` prints a
standalone probe for only the old finite-count lemma; it does not rerun the
stopped whole module. `connection --progress /tmp/NEW-connection-progress`
prints the current split connection with per-declaration progress markers.
Build `Physics.StandardModel.Operators.SMB1WeakCountArithmetic` first, save
stdout to a fresh /tmp Lean file and use the existing one-thread/300 s/
10 GiB/4 GiB-reserve guarded runner serially. No dependency or proof limit
is changed. Marker text is progress only: successful Lean exit and the
persistent strict audit are required for acceptance.

The [revision result](../../docs/topics/sm-b1-weak-connection/results.md)
proves all 326 finite-domain minima through the split connection. The old
stopped source and `--refined` diagnostic remain labelled by their historical
status; the new classification is established by active kernel-checked
theorems. Rerun localization when covered dictionary/support/arithmetic
interfaces change. Generated probes/logs stay outside source control.

## B1 minimum-dimension interval inventory

`b1-minimum-inventory.py --retained --rows` prints the complete 326-row
retained grade inventory using only the Python standard library. Run from
the repository root; output is diagnostic JSON, not a Lean proof input.
It reads existing witness syntax, reconstructs the unchanged natural cyclic
domain and combines charge/below-ten lower grades with selected witness
upper grades. Default mode reproduces the initial proposed inventory.
`--refined` labels an unverified weak/chirality lower-bound proposal; its
apparent 326 matches are **not proved minima**.

The [owning topic](../../docs/topics/sm-b1-minimum-classification/results.md)
records 160 proved exact minima and 166 retained intervals. Its stronger
weak connection stopped at the 10 GiB guard. The retained stopped text
`probes/b1-weak-envelope-stopped.lean.txt` is unverified and excluded from
active sources; do not rerun it automatically or use it as a premise.
The ordinary library and strict audit protect actual interval semantics.
Rerun this diagnostic when the covered dictionary, upper grades or assignment
domain change. No numerical/CSV verdict enters the Lean path.

These standard-library Python/source-template tools reproduce the bounded
[feasibility investigation](../../docs/topics/sm-support-evaluator-feasibility/results.md).
They do not export a library evaluator, import CSV answers, change Lean limits
or resume retired numerical certificates. Templates are text outside the active
module graph. Successful generated Lean files must be checked by Lean; generating
text is never acceptance. No new package or environment is needed.

From the repository root, materialize **one** probe and use the existing guarded
runner (one process/build at a time):

```sh
python3 tools/structural-support/probe.py controls > /tmp/sm-controls.lean
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --rss-limit-gib 6 --min-available-gib 4 /tmp/sm-controls.lean /tmp/sm-controls.log
```

Stages:

| stage | purpose / observed outcome |
| --- | --- |
| `direct` | expected failure: missing decision instances and noncomputable code generation; occupation sizes print 1,6 |
| `controls` | 28 named closed checks plus all-local-declaration strict transitive audit; passes |
| `q6` | adds the original Q6 Higgs-support check; initial closed check passed |
| `q18` | adds Q18; fails at unchanged kernel recursion depth, investigation stop |
| `neutral-zero` | local Q24,m14 negative candidate; **not run**, gated behind Q18 |
| `reject-positive` | intentionally false SU2 support assertion; must fail |
| `reject-negative` | intentionally false SU2 non-support assertion; must fail |
| `compiled` | even LLHH Boolean code generation fails on a noncomputable decision dependency |

`controls` audits every local declaration (including all named controls and
compiler-generated helpers) against exactly propext, Classical.choice and
Quot.sound. Failed candidates may produce Lean's recovery `sorryAx`; the audit
rejects that too. Treat nonzero exit codes as failures and inspect the actual
error: a timeout is not the expected logical rejection control.

Q0/Q6 metadata extraction uses Lean elaborator normalization and `rfl`
correspondence checks; it does not trust a Python transcription. Generic finite
decisions remain noncomputable for compiled evaluation. The script only prints
source, so output paths/logs remain the caller's responsibility. The guard's
memory values are sampled process-group RSS, not hard OS limits.

Do not run the deferred stress/107-row probes after a resource stop without a
new scope decision. Rerun relevant probes if the structural syntax, core
presentations, field dictionary, finite decision instances or Lean pins change.
Measurements distinguish cached-import Lean elaboration/kernel checks from
cold builds and from compiled evaluation. See the topic verification record.

## Authorized Q18 cause isolation

The [follow-up diagnosis](../../docs/topics/sm-support-evaluator-feasibility/diagnosis-results.md)
uses six separate component probes, without retrying the full Q18 failure or
raising options:

```sh
python3 tools/structural-support/diagnose.py metadata > /tmp/sm-diagnosis.lean
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --rss-limit-gib 6 --min-available-gib 4 /tmp/sm-diagnosis.lean /tmp/sm-diagnosis.log
```

Stages: `occupation6`, `occupation18`, `words18`, `metadata`, `spins`, `occupied`.
Only `occupation18` is expected to fail; inspect its kernel recursion diagnostic.
The `spins` projection deliberately discards color and is not an equivalent
support criterion. The `occupied` stage tests one fixed (6,6,6) occupied Q-core
expression, not the entire original Q18 space. Successful existence checks do
not establish exhaustive-search performance. `instances.lean.txt` retains the
selected-instance reconnaissance separately from the six component probes.

## Compact remedy prototype and independent color controls

[Remedy results](../../docs/topics/sm-support-evaluator-feasibility/remedy-results.md)
record uniform kernel proofs of triple membership and attainability in the
existing occupation type. The prototype is not wired into library decisions.

```sh
python3 tools/structural-support/remedy.py compact > /tmp/sm-remedy.lean
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --rss-limit-gib 6 --min-available-gib 4 /tmp/sm-remedy.lean /tmp/sm-remedy.log
```

Other stages are `color-positive` and `color-negative`, both expected to pass.
The former tests a symmetric/opposite-symmetric degree-six pair; the latter
rejects a single symmetric degree-six leaf. Neither enumerates occupations.
Every stage appends the existing strict all-local-declaration audit. Rerun if
counts, finite enumeration, color predicates or pins change. Do not interpret
the 190-entry length proof as an end-to-end Q18 support or performance result.

## Active compact occupation implementation

The [active implementation checkpoint](../../docs/topics/sm-support-evaluator-feasibility/implementation-results.md)
adds an explicit dependent-index enumeration and opt-in decisions in registered
Math/Physics modules. Unlike the earlier prototypes, Q18 and the neutral mixed
negative example are now kernel-checked active theorem declarations.

```sh
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build Physics.StandardModel.Operators.Audit.AuditSMCompactSupport /tmp/compact-audit.log --rss-limit-gib 6 --min-available-gib 4
```

`compact-cardinality.lean.txt` checks count 190/existence with the explicit new
occupation instance. `compact-rejections.lean.txt` contains intentionally false
positive/negative assertions using the new Higgs decision; both must be rejected
as false. Copy one text template to an explicit temporary `.lean` path and use
the same runner. These are not compiled all-content request solvers.
The full default-root build subsequently passed with an explicitly authorized
10 GiB guard (7325 jobs, no warnings); individual probes retain 6 GiB. The
prior 6 GiB full-build interruption remains recorded in the checkpoint.

## Complete remaining verification inventory

`check-remaining.py` validates the exact 107-key neutral domain against the
original unclassified table, checks neutral charge/parity conventions and input
hashes, then runs fresh compact decisions serially for all reference signs.
Two compiled controls and a larger neutral mixed negative precede the rows.
Each attempt retains exit, wall time, sampled group peak and diagnostic category.
No CSV answer is a theorem premise: its sign only proposes a closed statement.
A Lean error, time/RSS interruption or unsupported compilation remains unknown.

```sh
python3 tools/structural-support/check-remaining.py --output /tmp/sm-remaining.csv --metadata /tmp/sm-remaining.json --logs /tmp/sm-remaining-logs
```

Use a new explicit log directory; the runner refuses to overwrite one. It uses
10 GiB sampled group RSS, 4 GiB host reserve, 300 seconds per case, one Lean
thread and no concurrent Lean jobs. Sampling can overshoot a guard before the
child is interrupted. It stops the batch on reserve exhaustion, diagnostic
errors or a proposed-sign mismatch; independent resource-limited rows otherwise
continue. Review all outcomes, not just successful exits.

`neutral-certificates.py` proposes an independent all-107 proof file using the
existing symbolic weak cutoff for zeros and explicit occupation witnesses for
larger positive Q contents. It preserves actual joint source expressions.
Neither this path nor the primitive compiled controls implements a generic
compiled support API. Run the file only after the serial decision batch ends:

```sh
python3 tools/structural-support/neutral-certificates.py > /tmp/sm-neutral-certificates.lean
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py /tmp/sm-neutral-certificates.lean /tmp/sm-neutral-certificates.log --rss-limit-gib 10 --min-available-gib 4
```

Generated candidates and all helper declarations must pass kernel checking and
strict audits; printing a file or a reference sign does not certify anything.
`additional-controls.lean.txt` covers previously unrun conjugate metadata,
core overflow and empty-content checks. Raw generated sources/logs stay outside
source control; generators and explicit verification records are retained.

The [recorded remaining checks](../../docs/topics/sm-support-evaluator-feasibility/remaining-checks-results.md)
complete the 107-sign comparison through the independent certificate file:
41 positive/66 zero, 334 strict checks, 26.0 seconds, 5629024 KiB sampled peak.
The naive measurement sweep was stopped after 30 completed neutral rows
(9 matched, 21 memory interruptions); one in-flight row is labelled cancelled
and 76 raw rows remain unbenchmarked. This is not an all-107 raw-runtime success.
See [per-case measurements](results/remaining-naive.csv) and
[input hashes and summary](results/remaining-summary.json). Exact multiplicities,
ranks and original table statuses are unchanged. Additional controls pass with
14 strict checks and 5097732 KiB peak, including compiled/kernel count 703.
The independent certificates also prove the frozen mixed original-space negative
by the existing chirality theorem, while its raw decision remains resource-limited.

## 572-assignment certificates

The maintained opt-in verification target is:

```sh
python3 tools/structural-support/verify-assignments.py --output /tmp/NEW-sm-assignment-check
```

It refuses an existing output directory, checks retained input/source hashes,
compares the regenerated CSV, builds the repository imports serially, and
requires the final kernel/strict-audit marker. It also generates and checks
the historical 796 all-content degree certificates using `SMChargeDegreeBounds`.
They are independent cross-checks: `SMFiniteLeptonDegreeBounds` now proves the
uniform minimum-|L| bound, all row applications and their distributions in
the ordinary library build. Neither route determines minimum engineering
dimension. Measurements and logs
are written under the explicit output directory. It uses one Lean thread,
300 seconds per run, 10 GiB sampled group RSS and a 4 GiB host reserve.
Run this target when covered definitions/templates change and during their
pre-merge/merged-state verification. Ordinary `lake build` does not execute
it. No expected hash or table is automatically refreshed on a mismatch.

The subsequent [finite-charge theorem](../../docs/topics/sm-attainable-lepton-charges/README.md)
is a normal library API. `SMFiniteLeptonSupport.original_allowed_iff` and
`exact_original_iff` cover arbitrary nonzero k,q,l. `SMFiniteLeptonAssignments`
defines the candidate domain and flags inside Lean, proves complete unique
coverage, total 572 and the 326/144/102/0 class counts, and exposes original-space
B1/B2/request corollaries. No external row list or CSV enters the proofs.
Ordinary `lake build` protects those results and the 37 committed joint witnesses.
The table renderer was removed; the witness renderer remains checked byte-for-byte.
The opt-in verifier builds the persistent audit, compares an optional Lean export
to the historical CSV, then runs the older independent certificates. These
historical checks are separate from the Lean-owned proof path. The minimum
degree audit also runs before export; its default-build bounds do not depend
on the older degree-certificate generator.

To export a CSV from Lean, after building `SMFiniteLeptonDegreeBounds`, use:

```sh
python3 tools/structural-support/export-assignments.py --output /tmp/NEW-lean-assignments
```

The exporter needs no input CSV. An optional `--compare PATH` compares an
external snapshot without making it a proof premise. It uses the same
one-thread/300 s/10 GiB/4 GiB guard and refuses an existing output directory.
The CSV uses the library's computed minimum and chooses a corresponding
signed L for display, preferring the negative value in a tie. It contains calculated verdicts and that minimum-|L| choice;
that display does not determine minimum operator dimension. See the
[Lean enumeration extension](../../docs/topics/sm-finite-charge-support/lean-enumeration-plan.md).

The [maintenance topic](../../docs/topics/sm-finite-charge-support/README.md)
owns subsequent verification and degree interpretation. The historical
commands below still reproduce the original certificate alone.

`assignment-certificates.py` reassesses the exact existing 572-row domain
`2 ≤ k ≤ 12`, `3q+l ≠ 0`. It first reproduces the original CSV, counts and
151 unit orbits. Its finite arithmetic proposals are checked independently
against one full period of length `2k` and unit actions. Proposed signs never
enter Lean as premises: generated proofs use actual original coefficient
spaces, symbolic central parity/charge exclusion, and explicit joint-support
witnesses. Run serially:

```sh
python3 tools/structural-support/assignment-certificates.py > /tmp/sm-assignment-certificates.lean
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py /tmp/sm-assignment-certificates.lean /tmp/sm-assignment-certificates.log --rss-limit-gib 10 --min-available-gib 4
python3 tools/structural-support/assignment-certificates.py --csv > /tmp/sm-assignment-verdicts.csv
cmp /tmp/sm-assignment-verdicts.csv tools/structural-support/results/assignment-verdicts.csv
```

Only a successful kernel run including the final strict transitive audit
certifies the proposed table. The generator checks B1 prohibition, B2
prohibition/allowance, and the actual `b1ForbiddenB2Allowed` request separately
for every row. It does not compute ranks or multiplicities and does not make
the general noncomputable support decision executable. See the
[contract](../../docs/topics/sm-support-evaluator-feasibility/assignment-plan.md)
and [result](../../docs/topics/sm-support-evaluator-feasibility/assignment-results.md).

## Executable source-data diagnostics and stopped SM bridge

The retained Math modules construct core syntax and numeric generation/species
composition with ordinary structural correspondence proofs. No computational
support proof or general compiled support solver is added. The
[data-layer result](../../docs/topics/sm-support-evaluator-feasibility/data-layer-results.md)
records the partial endpoint and the 10 GiB stop at the complete SM bridge.
The candidate `probes/sm-joint-support-data-candidate.lean.txt` is **unverified**,
excluded from active module aggregates, and must not be used as a checked API.

The runtime-only smoke template reads the degree from an environment variable.
Its printed branch counts are diagnostics, never proof premises. With imported
modules already built, run serially:

```sh
cp tools/structural-support/probes/joint-source-data-smoke.lean.txt /tmp/joint-source-data-smoke.lean
LEAN_NUM_THREADS=1 SM_DATA_DEGREE=6 python3 tools/exact-rank/kernel-probe.py /tmp/joint-source-data-smoke.lean /tmp/joint-data-smoke6.log --rss-limit-gib 10 --min-available-gib 4
LEAN_NUM_THREADS=1 SM_DATA_DEGREE=13 python3 tools/exact-rank/kernel-probe.py /tmp/joint-source-data-smoke.lean /tmp/joint-data-smoke13.log --rss-limit-gib 10 --min-available-gib 4
```

Degree 6 prints Q/conjugate-Q counts 20 and two-species count 400; degree 13
prints zero for every listed overflow core/composition. Neither output proves
an allowed/forbidden coefficient. `AuditJointSourceData.lean` persistently
audits all 56 new named Math declarations; the ordinary proofs, not those
printed counts, establish correspondence to the mathematical presentations.

## Revised SM connection and downstream use

The active `SMCoreSourceData`/`SMJointSupportData` modules supersede the stopped
projection-comparison candidate. They put executable syntax in the outer
presentation field and connect support through the same actual full source.
New semantic proofs and ordinary consumer examples use no computational
support proof. See the [verified connection](../../docs/topics/sm-support-evaluator-feasibility/data-connection-results.md)
and [proof dossier](../../docs/proof/current/applications/Physics/SM_JOINT_SUPPORT_DATA.md).

After building imports, run serially under the frozen 120 s/10 GiB guard:

```sh
cp tools/structural-support/probes/sm-joint-data-consumers.lean.txt /tmp/sm-joint-data-consumers.lean
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py /tmp/sm-joint-data-consumers.lean /tmp/sm-data-fresh-consumers.log --rss-limit-gib 10 --min-available-gib 4 --timeout-seconds 120
cp tools/structural-support/probes/sm-joint-data-use.lean.txt /tmp/sm-joint-data-use.lean
LEAN_NUM_THREADS=1 SM_DATA_DEGREE=6 python3 tools/exact-rank/kernel-probe.py /tmp/sm-joint-data-use.lean /tmp/sm-data-runtime6.log --rss-limit-gib 10 --min-available-gib 4 --timeout-seconds 120
LEAN_NUM_THREADS=1 SM_DATA_DEGREE=13 python3 tools/exact-rank/kernel-probe.py /tmp/sm-joint-data-use.lean /tmp/sm-data-runtime13.log --rss-limit-gib 10 --min-available-gib 4 --timeout-seconds 120
```

The fresh consumer file proves five applications and audits them transitively;
it does more than print cached theorem types. Runtime degree input exercises
all ten signed core functions and numeric content composition; the balanced
Q18 expression has 8000 branches. Printed values are diagnostics, never proof
premises. Large-content component transport assumes the supplied joint
certificate, while the Q18/mixed allowance examples use existing algebraic
lemmas and explicit source/Higgs choices. Neither is an exhaustive search
benchmark or universal running-time guarantee.

For diagnosis only, `connection-probe.py --progress /tmp/NAME` regenerates the
OLD expensive comparison with a file progress marker. `--imports-only` emits
the import control instead. This diagnostic intentionally retains the failed
route; do not rerun it automatically or use its resource failure as a support
verdict. Current measurements, hashes and limits are retained in
[the evidence record](results/data-connection-summary.json).
