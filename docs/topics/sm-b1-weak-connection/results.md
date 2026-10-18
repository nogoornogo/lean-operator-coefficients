# Weak connection revision and complete finite-domain B1 minima

## Result

The revised connection and all 326 allowed-row B1 minima are proved. The
246 all-degree-forbidden rows retain None, and no allowed row is unresolved.
The previous resource stop and partial baseline remain valid evidence about
their own implementation; the old stopped source was not promoted to a proof.

The fixed ten signed three-generation SM species, independent Lorentz
actions, derivative-free statistics, neutral-residual Higgs/dual, scalar
cyclic q/l input and grading `3*n+2*(h+d)` are unchanged. Exact minima cover
every selected content, both baryon signs and all Higgs degrees on that input.

| Minimum derivative-free engineering dimension | Rows |
| ---: | ---: |
| 7 | 48 |
| 9 | 98 |
| 10 | 62 |
| 14 | 28 |
| 15 | 16 |
| 19 | 16 |
| 20 | 10 |
| 24 | 28 |
| 27 | 10 |
| 31 | 10 |
| All-degree forbidden, no numerical minimum | 246 |

`SMB1ExactMinima.minimum_distribution` kernel-proves these counts at doubled
grades 14/18/20/28/30/38/40/48/54/62. `classified_count` gives 326 allowed
entries. `row_minimum` supplies actual `IsMinimum` certificates for every
allowed row; `row_forbidden_below` excludes every smaller grading, for all
contents and either baryon sign. The inherited Lean-owned domain has unique
complete coverage of `2≤k≤12`, `q,l<k`, `(3*q+l)%k≠0`; no new row table is
introduced. This does not classify minimum dimensions for all cyclic inputs.

## Three-stage proof split

1. `SMB1WeakCountArithmetic` works on an abstract ten-component Nat count
   vector. Capacity sums and two explicit sums of nonnegative terms prove
   `abs(7*L-B3)≤12+3*n+2*(h+d)` from scalar hypercharge and weak bounds.
   The count arithmetic has no coefficient-space hypotheses or representation
   equivalences. A large unconstrained mixed arithmetic solve is avoided.
2. `SMB1WeakDimensionBounds` proves the total/charge dictionary sums separately
   and extracts the existing complementary weak-capacity bounds from actual
   support. The final connection applies the abstract arithmetic lemma and
   reexpresses its scalars; actual tensor carriers stay out of that proof.
3. `SMB1StrongDimensionBounds` combines this weak envelope with the existing
   charge/hypercharge envelope, capacities and independent-chirality grade
   congruence. Two separate pure signed arithmetic helpers yield lower grades
   on the 18 possible normalized odd lepton charges. `SMB1ExactMinima` takes
   their finite neutral minimum and matches the unchanged actual graded
   upper witnesses from `SMB1DimensionWitnesses` on every row.

The raw lower grade for normalized L is the maximum of
`3*(3+abs(L))`, `(3+abs(L))+2*abs(2*L-1)`, `max(7*L-15,0)` and
`max(-7*L-9,0)`, then adjusted by two when needed for the already proved
grade congruence. Its validity is proved, not assumed from the arithmetic
diagnostic. Normalization handles both baryon signs directly while retaining
the actual input's engineering grade; no source-conjugation theorem is assumed.

## Localization and its limits

The progress-instrumented old finite-count lemma passes alone in 4.5 seconds
at 5149832 KiB. The revised complete dictionary/support connection passes
directly in 5.0 seconds at 5134292 KiB, with an empty diagnostic log and its
last progress marker reached. The structured count module builds in 6.0 s
at 5245168 KiB; the actual connection plus strong signed lower bounds build
in 13.3 s at 5281252 KiB.

These checks separate finite-count arithmetic, support extraction and the
scalar consequence. They show these interfaces can be checked below the
unchanged guard. They do not identify every allocation in the old 69.9 s
interrupted run, provide a universal RAM bound, or diagnose a compiler defect.
The old full stopped module was not rerun. No resource stop occurs in this
revision and no proof/resource/dependency limit is raised.

The reproducible probe renderer is `tools/structural-support/b1-weak-localize.py`:

```sh
python3 tools/structural-support/b1-weak-localize.py counts --progress /tmp/NEW-count-progress > /tmp/NEW-count.lean
python3 tools/structural-support/b1-weak-localize.py connection --progress /tmp/NEW-connection-progress > /tmp/NEW-connection.lean
```

Build `SMB1WeakCountArithmetic` before the connection probe, then check each
file serially with the existing guarded runner at one thread, 300 seconds,
10 GiB sampled group RSS and 4 GiB host reserve. A progress marker by itself
does not imply acceptance: Lean must exit successfully, and persistent strict
audits check accepted interfaces. The corrected connection source regenerates
byte-for-byte. Disposable probes/progress/logs remain in /tmp.

## Development failures and trust boundary

The first progress probe used an unavailable unqualified `liftIO` identifier
(4.5 s, 5143972 KiB); it was corrected to the repository's existing
`run_cmd do IO.FS.writeFile` pattern. The first connection probe inserted
markers between documentation comments and their declarations and exposed
two finite-array reduction/association mismatches (4.5 s, 5132644 KiB).
The renderer now strips documentation comments in generated probes and uses
an `end-reached` marker, explicitly not a success verdict. The initial
row bridge confused Bool equality with decidable equality (14.0 s,
5894276 KiB); a standard equality simplification fixed it. These failures
are not successful baselines or memory stops.

All accepted new interfaces, importing consumers and the required complete
classification declarations have a persistent strict transitive audit. The
final audit covers 67 namespace declarations and their transitive dependencies,
including the private arithmetic helpers through their public consumers,
against exactly propext, Classical.choice and Quot.sound. No custom axiom,
allowlist exception, `sorry`, `native_decide`, supplied multiplicity/occurrence
law or numerical/CSV premise is used. Closed finite counts are checked in
the Lean kernel. Existing upper witnesses and all earlier proof modules
remain unchanged; no new witness or occupation search was started.

Final verification and source hashes are retained in
[machine-readable evidence](verification.json).

| Accepted final check | Seconds | Sampled group peak KiB |
| --- | ---: | ---: |
| All-row exact classification and initial audit | 19.0 | 5895940 |
| Final consumer/audit build: 67 strict checks | 8.8 | 5216580 |
| Direct audit re-execution: 67 strict checks | 4.8 | 5128876 |
| Fresh importing applications | 3.5 | 5100688 |
| Full default-root `lake build GUT`: 7364 jobs | 8.8 | 6701072 |

All accepted runs finish below the unchanged guards with zero warnings/errors.
Imports are cached; the first audit build includes the new complete row/count
source, while the final audit build adds the generic weak-envelope consumer.
The full build includes unchanged earlier audits as well as the new audit.
Layout passes 1978 modules. Link/diff, source-policy and probe reproducibility
checks are retained in the topic and JSON record. Statements, dossier and
assumptions agree. Historical witness/domain sources are unchanged, so unrelated
optional table-export regressions were not rerun. None of these measurements
is a universal runtime/RAM guarantee for arbitrary downstream proof terms.

## Scope and endpoint

The original finite-domain 326-minimum objective is achieved by this revision.
The historical 160-exact/166-interval module remains a valid weaker interface;
its earlier source and verification record are preserved. Its old diagnostic
`--refined` output remains labelled as a proposal at that checkpoint. Current
claims come from the new actual-space theorems and kernel row checks, not
from relabelling old diagnostic output.

Only the fixed 572-row B1 domain has complete minimum dimensions here.
The generic weak-envelope and lower-bound helpers do not imply a minimum
classification for arbitrary k, flavor actions, B2, derivatives/EOM/IBP or
other fields. Allowed coefficients do not establish UV generation, anomaly
freedom, matching, amplitudes or rates. Other proposed follow-ups remain
untouched. No master integration or push is authorized.

The verified result `checkpoint 01` was
[integrated into its recorded parent](integration.md) at `checkpoint 02`.
Fresh direct strict audit and the full cached build pass after integration;
the local child branch was safely deleted. No scoped obligation remains.
