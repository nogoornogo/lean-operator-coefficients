# Q18 structural support verification

The user selected replacing the old numerical equality with zero/nonzero
support. See the [plan](q18-support-plan.md) and [proved scope](q18-support-results.md).
Work continues on `proof/sm-computable-characters` after `checkpoint 01`; no merge,
push, dependency/pin change or new literature premise is authorized or used.

## Focused proof checks

All Lean commands set `LEAN_NUM_THREADS=1` and use the existing runner with
`--rss-limit-gib 6 --min-available-gib 4`. Builds/probes are serialized.

| Target | Result | Seconds | Sampled group peak KiB |
| --- | --- | ---: | ---: |
| `SelfDualCoefficient` | passed | 3.3 | 3365720 |
| `SMQ18Support` | passed | 5.0 | 4946780 |
| `SMCombinedChargeSupport`, including `FactoredInvariantSupport` | passed | 8.3 | 4971208 |
| `SMQ18LocalSupport` | passed | 7.0 | 4984236 |
| `AuditSMStructuralSupport`, including positive-dimension/symbolic-rank consumers | passed, 4196 jobs | 9.3 | 5284708 |
| `AuditStructuralExteriorSupport` | passed, 4010 jobs | 4.5 | 5163892 |

The Math audit covers 39 strict transitive standard-axiom checks; the Physics
audit covers 43, for 82 total, with layer and numerical-import checks intact.
New consumers are actual local coefficient/kernel permission and symbolic
rank deficiency, not asserted/evaluated multiplicities. Their proof signatures
contain no Weyl extraction input. No large closed Q18 reduction was executed.

An initial source-equivalence proof transported a dependent source type
through a whole representation equality. A bounded probe stopped at 22.6 s,
6299640 KiB; a preceding variant stopped at 22.8 s, 6296544 KiB. Neither probe
is accepted. The retained proof instead constructs the linear equivalence
explicitly and proves intertwining using an equality of linear operators.
Generic scalar-action/group-extension lemmas also avoid repeated unfolding
of the full SM representation. Early default-heartbeat/type-inference errors
were resolved with explicit parameters and these abstract interfaces; no
resource option or stopping budget was raised. Only checked proofs remain.

## Retirement integrity

The 13 old Q18 modules and the old consumer/audit snapshots are retained as
UTF-8 text, with paths and SHA-256 hashes in the
[archive manifest](archive/q18-numerical/manifest.json). All 15 snapshots were
checked byte-for-byte against the archived source at the recorded checkpoint and their
manifest hashes. Active numerical Q18 imports/consumers were retired at the
user's explicit change of endpoint; the new structural consumers are covered
by the strengthened structural audit. Other numerical examples retain their
statements. No audit allowlist or axiom policy was relaxed.

## Project-wide checks

Layout passed for 1678 modules. A first serialized monitored full build reached
the 300 s wall-clock stop, sampled peak 6254160 KiB. Its continuation stopped
at 137.5 s and 6311888 KiB after crossing the 6 GiB sampled group threshold.
Neither attempt is a successful full build. A no-build preflight then named
only `SMComputableCharacterExamples`, `SMCoefficientAssembly` and
`SMNeutralSparseExamples` as the remaining stale frontier. No retired Q18
module was a build target.

The generic assembly module passed separately (4.8 s, 5052908 KiB). The
remaining retained numerical controls were checked one module at a time:
`SMComputableCharacterExamples` stopped at 19.8 s, 6331936 KiB, and
`SMNeutralSparseExamples` stopped at 13.1 s, 6305236 KiB. Both crossed the same
6 GiB sampled stopping threshold; these are not Lean counterexamples or
successful checks. The examples' non-Q18 statements were left unchanged.
Their exact failing declaration was not inferred from the empty compiler
logs. These numerical controls are not imports or premises of the new Q18
proof, as enforced by the structural audit.

No further replay or budget increase was attempted. **The full-project build
and the modified sparse numerical audit remain outstanding at this resource
boundary.** The Q18 support theorem and its strengthened structural audits
have the focused verification recorded above; this checkpoint does not claim
a successful full build or completion of the broader Q/L classification.
A final no-build preflight returned 3 with exactly the two retained numerical
example modules as stale frontier targets. The generic assembly was up to
date, and no Q18 numerical module remained in the graph.
The final focused no-build check of both structural audit roots passed
(4316 jobs, all targets up to date), confirming the checked Q18 source closure
is unaffected by retirement of the numerical modules.

Documentation links passed for 865 Markdown files, 5349 local links and 109
fragments, zero errors (read-only retry for the sandbox `git ls-files`
restriction). Diff checks pass. The five new proof modules contain no
`sorry`, custom axiom, `native_decide`, `implemented_by` or `decide`.
The runner's eight small process controls passed. All archived snapshot hashes
and original-source comparisons passed. The root README, both CSVs,
Lean/dependency pins and Weyl premise are unchanged.
