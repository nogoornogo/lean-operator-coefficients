# Exact rational rank certificates

`certify.py` uses only Python's standard library. It performs exact rational
row reduction and emits a rank factorization, a left inverse of the column
factor and a right inverse of the row factor. Every identity is then checked
by `decide +kernel` in the generated Lean source. The generator is not trusted.

    python3 tools/exact-rank/certify.py tools/exact-rank/examples.json
    python3 tools/exact-rank/certify.py tools/exact-rank/examples.json --check Math/LinearAlgebra/Constructions/ExactRankCertificateExamples.lean
    lake build Math.LinearAlgebra.ExactRankCertificateExamples

Input is a JSON list of matrices with explicit `rows`, `cols`, `entries`.
Entries must be integers or strings such as `"1/2"`; floats are rejected.
Explicit dimensions also support zero rows/columns. Output goes to stdout.
The checked examples cover rectangular rank deficiency, fractions, a pivot
row swap, full rank, zero rank, and empty dimensions.

The theorem transports the certificate to complex numbers. This is not an
algorithm for arbitrary abstract complex entries, nor a proof that every SM
constraint matrix has rational entries. Large certificates can exceed Lean's
normal resource limits; no limit changes or numerical zero thresholds are used.

## Actual constant-species SM ranks

`constant-content-table.lean` exports the executable Lean classifier
`SMConstantContentRanks.evaluate`. Its `evaluate_sound` theorem proves that
every returned number is the actual local rank. `none` exports as an empty
rank cell, labelled `unclassified`, never as zero.

    lake build Physics.StandardModel.Operators.Audit.AuditSMNumericalRanks
    lake env lean tools/exact-rank/constant-content-table.lean
    lake env lean tools/exact-rank/constant-content-table.lean | cmp - tools/exact-rank/constant-content-ranks.csv

The committed CSV covers positive constant-species contents within each
species capacity, `0 <= m <= n*doubletCount(species)`, and
`delta=m,m-2,...,-m`. It has 19268 entries: 19161 known ranks and 107 unknown
neutral entries. It excludes mixed-species contents and the empty content.
Of the known ranks, 19160 follow from parity or charge; the one nontrivial
neutral certified row is LLHH (1 of 108 even neutral entries).
Counts are not an all-content coverage percentage. Columns/dimensions and
charge/parity rank formulas are proved in Lean; no rationality premise on
the original finite-test matrix is used. The local group has trivial residual
input here, so the table is before residual invariance or q/l selection.

## Six-coordinate Weyl specialization regression

    python3 tools/exact-rank/check-sm-weyl.py

This standard-library, exact-integer diagnostic uses color weights
`(1,0),(0,1),(-1,-1)` for `diag(z0,z1,(z0*z1)^-1)`, followed by weak,
left-spin, right-spin and integral hypercharge coordinates. Its six positive
roots match [SMCompactTorus](../../Physics/StandardModel/Operators/Support/Decomposition/SMCompactTorus.lean).
Gauge duals negate gauge weights; conjugate species exchange the active spin
factor, as in [the signed dictionary](../../Physics/StandardModel/Operators/BaryonOne/Inputs/DeltaLOneSignedFields.lean).
Three flavor copies repeat each slot. A Higgs constituent has weak weights
`m,m-2,...,-m` and hypercharge `3*delta`.

The grouped exterior DP expands `product(1+t*x^weight)^copies` with binomial
coefficients. Complement subsets handle upper exterior degrees; hypercharge
remains the homogeneous `n*Y` rather than being discarded. Positive-root
differences extract the constant term of the **inverse** source/Higgs
character. All 19161 certified constant-content CSV ranks are compared with
`columns - extracted multiplicity`; none of the CSV values is rewritten.

Controls cover all ten species, binomial dimensions, empty/top powers,
independent subset enumeration at degrees 0, 1, 2, dimension-1 and dimension,
color/weak/spin reflections, conjugate gauge/chirality conventions, LLHH and
conjugate LLHH, a Q upper-degree vanishing control, and distinct-species DUQL
and conjugate-pair spin controls. The unknown rows give 41 positive and 66
zero extracted values as an external diagnostic only. These rows remain
`unclassified` in the certified table.

The dictionary is transcribed from the linked Lean sources; this tool does
not prove their weights, `Presents`, the Weyl law, or a semantic connection
to an actual kernel. It is not a Lean proof, theorem premise, executable
all-content classifier, or q/l request solver. Rerun and review the dictionary
when the torus, roots, species, flavor count, Higgs action or CSV changes.
Run with ordinary `python3` (assertions enabled). No extra dependencies,
floating-point tolerances or generated rank certificates are used.

## Sparse Lean evaluation of the neutral remainder

    lake build Physics.StandardModel.Operators.Audit.AuditSMSparseCharacter
    lake env lean tools/exact-rank/sparse-neutral-table.lean | cmp - tools/exact-rank/neutral-sparse-results.csv
    python3 tools/exact-rank/check-sm-weyl.py

`neutral-sparse-results.csv` is a separate exact compiled Lean output for the
107 unresolved rows of the original table. Its columns are species, fermion
count, weak degree, hypercharge delta, carrier columns, extracted multiplicity
and conditional rank. The input list is proved to equal the original bounded
unresolved domain. The sparse evaluator's coefficient preservation and actual
kernel/rank connection are proved uniformly; the latter retains the explicit
Weyl reduction input. The Python diagnostic checks all 107 outputs, including
their keys, dimensions, multiplicities and ranks (41 positive, 66 zero).

Execution and regression agreement alone are not kernel-checked certificates
for the closed numerical values. Neither CSV is imported as a theorem premise;
the original unconditional CSV and its statuses are unchanged. See the
[sparse result](../../docs/topics/sm-computable-characters/sparse-results.md)
and its verification record for the precise arithmetic boundary. This is no
exhaustive mixed-content or q/l request search.

## Kernel-oriented refinement and bounded probes

The sparse exporter now uses the proved Higgs-string/A2 cancellation, a direct
exterior row for constant species, checked slot data and mathlib's proved fast
binomial formula. `SMNeutralSparseRanks.solveDirectWith_data` proves equality
to the original evaluator. The CSV schema and values are unchanged. Q6 has a
kernel-checked result; the later coefficient decomposition below also
closes Q18,m6,delta=-6. The all-107 certificate remains open. See the [result](../../docs/topics/sm-computable-characters/kernel-results.md)
and [verification](../../docs/topics/sm-computable-characters/kernel-verification.md).

    lake env lean tools/exact-rank/kernel-weight-data.lean | cmp - Physics/StandardModel/Operators/Support/Coordinates/SMKernelWeightData.lean
    python3 tools/exact-rank/kernel-neutral-target.py 0 18 6 -6 > /tmp/q18-target.lean
    python3 tools/exact-rank/kernel-probe.py /tmp/q18-target.lean /tmp/q18-target.log

Build the imported modules first. The target generator emits a closed
`decide +kernel` candidate using one row of the separate output CSV. Its values
are not premises: only a successful Lean check proves the candidate equality.
Use `0 6 2 -2` for the successful Q6 control. The generator rejects keys outside
the bounded 107-row table. No limit increases or additional dependencies.

The optional Linux-only runner samples combined process-group RSS and stops
at 16 GiB or 300 seconds, returning failure on interruption. These are external
diagnostic budgets, not Lean resource-option changes. It never turns a timeout,
interruption, or numeric execution into a proof. The slot-data generator emits
candidate definitions and an equality checked by the normal Lean build.

### Grouped weights and coefficient certificates

`SMGroupedCharacter` provides two further equivalent constant-species
backends: a degree-truncated `1,3,3,1` transition for three equal flavor
weights, and a coefficient-only recurrence. Proved linear support bounds
justify pruning the latter. `solveGrouped_eq` and `solveBounded_eq` identify
both with the original `solve`; actual dimensions/ranks keep the same Weyl
input. The direct sparse exporter and both CSVs are unchanged.

    python3 tools/exact-rank/kernel-neutral-target.py 0 18 6 -6 --backend grouped > /tmp/q18-grouped.lean
    python3 tools/exact-rank/kernel-neutral-target.py 0 18 6 -6 --backend bounded > /tmp/q18-bounded.lean
    python3 tools/exact-rank/kernel-coefficient-target.py 0 18 6 -6 --index 0 > /tmp/q18-coefficient.lean
    python3 tools/exact-rank/kernel-probe.py /tmp/q18-coefficient.lean /tmp/q18-coefficient.log

The coefficient generator transcribes the reduced extraction's 48 queries and
uses `check-sm-weyl.py` only to propose integers. Each integer gets a closed
`decide +kernel` goal. The composition theorem rewrites those proved values
and returns to the original evaluator; no Python value or CSV cell is a
premise. `--index 0..47` isolates a query, while `--chunk 0..11` emits four
queries. `--chain-prefix MODULE` makes chunk N import `MODULEPart(N-1)`;
`--compose-only MODULE` emits the consumer importing all twelve parts. This
chain also serializes expensive checks in a clean Lake build.

For the historical numerical checkpoint, the command below regenerates a
Q18 part for comparison with its [archived source snapshot](../../docs/topics/sm-computable-characters/archive/q18-numerical/README.md).
These are no longer active Lean targets. Use the same first four numeric arguments and
`--compose-only Physics.StandardModel.Operators.SMNeutralCertificates.Q18`
for the composition module.

    python3 tools/exact-rank/kernel-coefficient-target.py 0 18 6 -6 --chunk 0 --chain-prefix Physics.StandardModel.Operators.SMNeutralCertificates.Q18

`--split-depth 1..12` instead emits a shared graph of checked recurrence
states. A depth-2 L4 control passed, but the depth-8 first-Q18-coefficient
probe exceeded 300 seconds. That large generated graph is not retained.
The ordinary chunked route has much smaller source artifacts. See the topic's
[verification record](../../docs/topics/sm-computable-characters/kernel-verification.md)
for accepted and interrupted probes. Each module still needs successful
kernel checking; generating its source is not acceptance.


The assembly consumer is proved first for an abstract coefficient function,
then connected through `SMCoefficientAssembly.factor`. This named interface
avoids reducing the expensive closed function during elaboration; limits are
unchanged. At checkpoint `f81689ce`, Q18's 48 coefficients and original result equality were checked, with
maximum observed group RSS about 13.4 GiB. A subsequent whole-Q12 probe still
hit 16 GiB, so the full 107-row arithmetic certificate remains open.

As a rejection control, the L4 request `3 4 4 4 --index 2` proposes zero for an
inactive-spin query. Changing that candidate to one must fail kernel checking;
it was rejected as false. Candidate generation alone never accepts a value.

## Guarded structural proof checks

The structural Q/L route does not evaluate the character recurrence or a
numerical rank. Its audits reject imports of the sparse/grouped evaluators,
closed neutral certificates and the numerical constant-content rank module.
See the [revised structural plan](../../docs/topics/sm-computable-characters/structural-plan.md).

    LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build --rss-limit-gib 6 --min-available-gib 4 Math.RepresentationTheory.Audit.AuditStructuralExteriorSupport /tmp/structural-math.log
    LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build --rss-limit-gib 6 --min-available-gib 4 Physics.StandardModel.Operators.Audit.AuditSMStructuralSupport /tmp/structural-physics.log
    python3 tools/exact-rank/test-kernel-probe.py

Run one command at a time. `LEAN_NUM_THREADS=1` limits the inherited Lean task
pool; the group RSS budget still covers all subprocesses that Lake starts.
The runner refuses launch below the requested host `MemAvailable` reserve
and interrupts if that reserve is crossed during execution. Polling every
0.25 seconds is not a hard memory limit: the sampled value can overshoot the
threshold, and memory used by unrelated applications can change between
samples. An interrupted check is a failure, never a proof certificate. The
eight small runner controls cover successful/failed child exits, time/RSS
stopping, memory/cache refusal before launch and invalid budgets; they neither invoke Lean
nor create large allocations.

The remaining numerical examples retain their original definitions and
statements. The user-approved [Q18 structural replacement](../../docs/topics/sm-computable-characters/q18-support-results.md)
retires Q18's exact numerical statements as archived source text. A full-project rebuild may still check them; passing the two
structural audits does not make their arithmetic cheaper. Do not run a second
Lean probe alongside a build or launch a numerical replay as part of a
structural-only check. The normal full-build acceptance gate is retained.

For subsequent guarded full-project checks, require the other retained
numerical examples to be up to date first:

    LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build --rss-limit-gib 6 --min-available-gib 4 --require-cached Physics.StandardModel.Operators.SMComputableCharacterExamples --require-cached Physics.StandardModel.Operators.SMNeutralSparseExamples GUT /tmp/structural-full.log

Each `--require-cached` preflight uses `lake --no-build build MODULE`; a stale
certificate or dependency refuses launch of the subsequent build. It never
accepts an unverified value or changes Lake's cache metadata. A refused full
check remains outstanding; it is not a successful full build. The guard is
opt-in: a bare `lake build` still follows the repository's complete imports.

The old closed character/rank example proofs are archived as text and are no
longer build targets. `python3 tools/exact-rank/check-retired-certificates.py`
checks all archived snapshot hashes, absence of the retired source modules
and absence of their imports in the active Math/Physics/GUT graph. It uses
only Python's standard library and local files, never runs Lean, and makes
no claim to prove the archived numerical equalities. See the
[retirement record](../../docs/topics/sm-computable-characters/archive/remaining-numerical/README.md).
