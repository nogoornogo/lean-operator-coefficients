# Kernel refinement verification

Q18 arithmetic checks below describe checkpoint `checkpoint 01`. The user subsequently
selected its [structural support replacement](q18-support-results.md); the thirteen
Q18 source artifacts and old consumers are now [archived text](archive/q18-numerical/README.md),
not current full-build targets. Other bounded check records retain their scope.


## Bounds and unsuccessful variants

Probes are serialized. The optional Linux process-group monitor
`tools/exact-rank/kernel-probe.py` samples combined Lake/Lean RSS and interrupts
at 16 GiB or 300 seconds. These are diagnostic stopping choices, not Lean
resource-option changes or evidence of impossibility. Sampled RSS is not an
exact peak. Interruptions below are operator/monitor interruptions, not Lean
counterexamples or default-limit errors.

| Variant | Outcome |
| --- | --- |
| Nested structural merge, Q6 original result | Passed, 56.6 s |
| Nested structural merge, Q18 original result | Interrupted at 99.7 s, about 16 GiB group RSS |
| Weak-string cancellation prototype, Q6 multiplicity | Passed, 42.8 s, about 9.7 GiB group RSS |
| Core proof-producing `decide_cbv`, Q6 | Default 100000-step limit, 7.3 s; no limit increase |
| Split literal source with checked input weights, Q6 source/multiplicity | Passed, 114.2 s, about 7.7 GiB group RSS |
| Split literal source, Q18 | Interrupted at 300.3 s, about 5 GiB group RSS |
| Monomorphic literal source, Q18 | Interrupted at 111.0 s, about 16 GiB, before completion of the data stage |
| Quoted-data construction, Q18 | Interrupted at 109.5 s, about 16 GiB, before completion of the data stage |
| Direct final-form lookup before explicit primitive recursors, Q18 | Interrupted at 81.2 s, about 16 GiB; fast binomial rewrite already applied |
| Final explicit primitive recursors, direct exterior row and fast binomial, Q18 | Interrupted at 99.4 s, about 16 GiB |

The first nested-recursion prototype regressed compiled execution and was
replaced. Large literal definitions also hit default elaboration heartbeats;
splitting declarations and caching decidable-equality instances addressed that
issue without raising limits. No unfinished source-table theorem, raw
declaration injection or auxiliary generated exterior table is retained in
repository sources.

Inspecting elaborated definitions revealed `Nat.brecOn` / `List.brecOn` in
the superficially structural versions. The final implementation uses explicit
primitive recursors instead. The `Nat.choose` recursion was another independent
obstacle for numerical rank equalities; its existing mathlib fast-computation
theorem is used explicitly. These refinements are proved equalities, not added
assumptions. Early syntax/elaboration failures were corrected before acceptance.

## Final checks

The final `SMNeutralSparseExamples` build passed (29 s), including the new Q6
result equality, transport to the original `solve`, conditional actual kernel
and rank, and Q18's fast/original column equalities. The closed calculations
use `decide +kernel`. No Q18 full-result or all-107 arithmetic theorem is
claimed. The final Q18 probe's log was empty on interruption; no completed
certificate was inferred from it.

    lake build Math.RepresentationTheory.Audit.AuditSparseWeightPolynomial Physics.StandardModel.Operators.Audit.AuditSMSparseCharacter
    lake build
    lake env lean tools/exact-rank/sparse-neutral-table.lean | cmp - tools/exact-rank/neutral-sparse-results.csv
    lake env lean tools/exact-rank/kernel-weight-data.lean | cmp - Physics/StandardModel/Operators/SMKernelWeightData.lean
    python3 tools/exact-rank/check-sm-weyl.py
    python3 tools/exact-rank/check-lepton-weights.py
    python3 tools/exact-rank/certify.py tools/exact-rank/examples.json --check Math/LinearAlgebra/ExactRankCertificateExamples.lean
    node tools/layout/check-layout.mjs
    node tools/docs/check-links.mjs
    git diff --check
    git diff --cached --check

Focused build passed, 4427 jobs, with 21 Math and 54 Physics strict transitive
standard-axiom checks and import-layer checks. Full build passed, 7012 jobs.
Final focused/full logs have zero warning/error lines. The Lean output and
checked slot-data regeneration each matched their committed artifacts byte
for byte, with `pipefail` enabled.

The exact diagnostic matched all 19161 known original rows and all 107 sparse
output rows (41 positive, 66 zero); 169 lepton pairs and exact rational
certificate regeneration passed. Layout passed for 1650 modules. Final links
passed for 856 Markdown files, 5274 local inline links and 106 heading
fragments, zero errors (approved read-only retry after a sandbox `git`
subprocess denial). Diff checks passed; the staged diff is rechecked before
the topic commit.

Both Python tools passed syntax checks. The target generator reproduced the
Q6/Q18 closed goals. The runner returned success for a kernel-proved `2+2=4`
control and failure for a rejected `2+2=5` control (each about 1.3 s). The
persistent runner was also used for the final primitive-recursion Q18 probe;
its later cleanup/readability refactor retained the same monitoring protocol.

The original unconditional CSV, separate sparse CSV, root README, Lean and
dependency pins, Weyl premise and audit allowlists remain unchanged. No merge
or push occurred.


## Grouped / coefficient-only continuation

The later user-authorized pass retains the same monitor and theorem inputs.
The grouped transition and fixed degree truncation are proved against the
original exterior recurrence. Linear support bounds justify every pruned
coefficient branch, and `solveBounded_eq` proves equality to the old evaluator.
No diagnostic number is a premise.

| Probe | Outcome; sampled process-group peak |
| --- | --- |
| Grouped Q6 result | Passed, 19.5 s; 7208572 KiB |
| Grouped Q18 result | Interrupted, 107.5 s; 16782028 KiB |
| Coefficient-only Q6 result | Passed, 29.5 s; 8904984 KiB |
| Coefficient-only Q18 result | Interrupted, 89.9 s; 16785628 KiB |
| Individual Q18 coefficient at `(0,0,-6,0,0,-18)` | Passed, 88.6 s; 13823428 KiB; value 8561154 |
| Shared recurrence states for that coefficient, depth 8 | Interrupted at 300.1 s; 7675928 KiB |
| Shared-state L4 control and result composition, depth 2 | Passed, 7.0 s; 5220896 KiB |

The shared-state generator needed explicit list-head and canonical query
arguments for rewriting; those initial elaboration failures were corrected.
No large unfinished state table is retained. The successful individual query
motivates four-query modules with chained imports, so fresh Lake builds also
serialize the expensive kernel checks. `kernel-probe.py --build` applies the
same 16 GiB / 300 s monitor to one Lake module. The accepted chunk results are below.


### Accepted Q18 decomposition

All twelve four-query modules passed. Chained imports serialize their expensive
kernel checks in a fresh build. Their summed monitored wall time was 980.6 s;
this trades total work for bounded peak memory, not a Q18 speedup claim.

| Part | Monitored seconds | Sampled group peak, KiB |
| --- | ---: | ---: |
| 0 | 115.4 | 14059280 |
| 1 | 102.2 | 13162276 |
| 2 | 101.7 | 12419220 |
| 3 | 98.7 | 11815612 |
| 4 | 95.4 | 11988856 |
| 5 | 92.4 | 11539812 |
| 6 | 66.1 | 9986100 |
| 7 | 62.9 | 9651592 |
| 8 | 66.9 | 10035812 |
| 9 | 67.1 | 9779780 |
| 10 | 56.4 | 9183768 |
| 11 | 55.4 | 8961676 |

The first direct composition and a function-parameter helper each hit the
default 200000-heartbeat elaboration limit (23.0 / 23.3 s). No limit was raised.
Adding the named, uniform `SMCoefficientAssembly.evaluate` / `factor` interface
avoids expanding the closed coefficient function during assembly unification. The final composition module
passed in 7.3 s, peak 5061724 KiB, including the new factor module build.
This closes multiplicity 33573 and rank 63525913527 for Q18,m6,delta=-6,
and transports them to the original `solve`.

Focused build passed, 4444 jobs: 32 Math and 65 Physics strict transitive
standard-axiom and import-layer checks. Actual Q18 kernel/rank consumers retain
the Weyl input. There were no warning/error lines in the final focused log.
A deliberately wrong L4 inactive-spin coefficient (candidate 1 instead of 0)
was rejected by `decide` as false (exit 1, 3.5 s), demonstrating that generation
and file creation do not accept a candidate. All thirteen final Q18 source
artifacts regenerate byte-identically.


### Continuation stop

The additional coefficient-only whole-Q12,m4,delta=-4 probe was interrupted at
141.5 s and 16781968 KiB sampled group RSS. Its log was empty; there is no
accepted closed Q12 result. The pass stops here rather than subdivide further
rows repeatedly. Q18 is accepted through the independently checked coefficient
composition; the all-107 arithmetic certificate remains open. This does not
prove an inherent computational limit for Q12 or the remaining rows.


### Final regression checks

`lake build` passed, 7029 jobs, with no warning/error lines. The final generated
L4 shared-state/assembly control also passed (6.8 s, 5148264 KiB), checking the
final template rather than relying on an earlier prototype.

Both constant-content and sparse-neutral Lean CSV exports matched their
committed files byte for byte with pipeline failures enabled. Checked slot-data
regeneration also matched exactly. The independent Python diagnostic matched
19161 original known entries and all 107 sparse entries (41 positive, 66 zero);
all 169 lepton pairs and exact rational certificate regeneration passed.
The 13 final Q18 source modules regenerate byte-identically. All three Python
tools parsed; five invalid coefficient-generator requests were rejected.

Layout passed for 1667 modules. Local links passed for 856 Markdown files,
5277 inline links and 106 heading fragments, zero errors (read-only retry after
a sandbox git-subprocess denial). Final diff and staged
diff checks are performed before the commit. The root README, both CSVs,
Lean/dependency pins and audit allowlists are unchanged. No merge or push.
