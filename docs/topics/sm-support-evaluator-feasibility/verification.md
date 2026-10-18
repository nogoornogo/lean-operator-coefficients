# Feasibility verification — stage 01

Branch `audit/sm-support-evaluator-feasibility`, base `checkpoint 01`.
All measurements use already cached imports, `LEAN_NUM_THREADS=1`, 300-second
wall cap, 6 GiB sampled process-group RSS cap and 4 GiB host memory reserve.
No concurrent Lean run, proof-limit increase or numerical evaluator was used.
These are elapsed times for the complete generated probe file (including its
small controls), not isolated target timing or cold library-build costs.

## Command and measurements

Materialize a stage via `python3 tools/structural-support/probe.py STAGE` into
an explicit `/tmp/NAME.lean` path, then run:

```sh
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --rss-limit-gib 6 --min-available-gib 4 /tmp/NAME.lean /tmp/NAME.log
```

| check | exit | seconds | sampled peak KiB | result |
| --- | --- | --- | --- | --- |
| Route A `direct` | 1 | 3.5 | 5041136 | missing instances and noncomputable metadata code generation; occupation sizes 1,6 printed |
| Route B initial SU2/reflection | 0 | 4.0 | 5383724 | CG true/false kernel checks, Q0/Q6 metadata equalities, branch sizes 1,20 |
| initial original-space and local controls | 0 | 6.5 | 5682764 | actual allowance/prohibition plus local and conjugate checks |
| remaining four sector controls | 0 | 7.5 | 5691748 | DUQL/QQUE/QQQL/DUUE Higgs predicates |
| Q6 closed Higgs predicate | 0 | 12.8 | 6257832 | `decide +kernel` passed at h=0,d=2 |
| Q18 closed Higgs predicate | 1 | 8.8 | 5717848 | kernel deep recursion; stopped this route |
| final named `controls` plus strict audit | 0 | 8.3 | 5719516 | 28 named checks and 79 local declaration audits passed |
| `reject-positive` | 1 | 8.0 | 5717680 | false positive candidate rejected |
| `reject-negative` | 1 | 8.0 | 5722752 | false negative candidate rejected |
| `compiled` | 1 | 8.3 | 5720548 | LLHH `#eval` depends on noncomputable `higgsDecision`; 79-declaration audit still passes |

The Q6 run preceded adding names/audit to all controls. Its original closed
kernel proof passed; the generator now gives the same candidate a name and
includes it in the audit. This final Q6 variant was not rerun after the Q18
stop. No final-audit success for that variant is asserted.

Q18 stopped on Lean's existing recursion-depth limit, not the external
300-second or RSS guard. It was not retried. No Q24 zero stress probe or
107-row comparison was run. Post-stop runs only verified the retained small
controls and rejection/code-generation diagnostics; they did not resume stress
search or try another refinement.

Development corrected ordinary compilation issues: color/joint/content/Higgs
instances had to be declared noncomputable, and the audit's mutable counter
needed an explicit `Nat` type. These are not support counterexamples. The
failed logical/resource candidates also fail the strict audit because Lean
error recovery introduces `sorryAx`; no such candidate is accepted or imported.
The final audit permits only propext, Classical.choice and Quot.sound, without
new exceptions. The proof-bearing metadata normalizer is checked by two `rfl`
correspondences, not trusted as an oracle.

## Repository acceptance

- Python generator parses successfully with Python's standard-library AST.
- No `sorry`, custom axiom declaration, `native_decide`, `implemented_by` or
  raised recursion/heartbeat setting in either retained Lean template.
- `node tools/layout/check-layout.mjs`: 1934 modules; all checks pass.
- `python3 tools/exact-rank/check-retired-certificates.py`: 19 snapshot hashes,
  15 retired modules absent and active imports pass.
- `node tools/docs/check-links.mjs`: 962 Markdown files, 5885 local links,
  111 heading fragments, zero errors. Required an escalated rerun after the
  sandbox blocked its read-only git subprocess (`spawnSync git EPERM`).
- `git diff --check`: passed, including the staged change review.

All retained Lean inputs are diagnostic text templates outside the active
module graph. No Math/Physics/GUT source, aggregate, theorem premise or pin
changed. No full `lake build` or library audit rebuild was rerun; no new library
proof baseline or production evaluator is claimed. The strict all-local probe
audit checks the transitive axioms of the declarations actually introduced in
the successful experiment. Raw build logs remain outside source control.

The investigation endpoint is a bounded feasibility decision with a recorded
stop, not acceptance of a scalable evaluation theorem. Historical/final review
documentation elsewhere remains intentionally untouched. No merge or push.
