# Sparse continuation verification

## Proof and execution boundary

The sparse arithmetic, shared-table coefficient equality, actual presentation
and uniform conditional kernel/rank/support consumers are proved in Lean.
The 107-row input enumeration is checked with `decide +kernel`. Small controls
in `SMNeutralSparseExamples` use the same kernel reduction, including cached
L4 and conjugate LLHH, and conditional actual L4 kernel/rank consequences.

The complete numerical CSV is exact compiled Lean output, not a theorem
asserting its 107 closed numerical equalities. A single
`results = expected` certificate using `decide +kernel` was attempted on resume.
After about 206 seconds it used roughly 18 GB RSS and was interrupted with
SIGINT to keep verification bounded (Lean exit 130). This was an operator
interruption, not a reported Lean default-limit error or a counterexample.
The unfinished certificate source was removed; no `sorry`, custom axiom,
native proof axiom or changed resource flag replaced it. The earlier
interrupted run had no completion evidence and is not counted as a pass.

No all-107 closed arithmetic theorem is claimed. Efficient proof certificates
for those values require another implementation strategy; the proved uniform
evaluator and its exact executable outputs are retained at the plan's stop
gate. Full q/l request-domain search also remains separate.

## Commands

    lake build Math.RepresentationTheory.Audit.AuditSparseWeightPolynomial Physics.StandardModel.Operators.Audit.AuditSMSparseCharacter
    lake build
    lake env lean tools/exact-rank/sparse-neutral-table.lean | cmp - tools/exact-rank/neutral-sparse-results.csv
    python3 tools/exact-rank/check-sm-weyl.py
    python3 tools/exact-rank/check-lepton-weights.py
    python3 tools/exact-rank/certify.py tools/exact-rank/examples.json --check Math/LinearAlgebra/ExactRankCertificateExamples.lean
    node tools/layout/check-layout.mjs
    node tools/docs/check-links.mjs
    git diff --check
    git diff --cached --check

Focused build passed, 4424 jobs, including 9 Math and 34 Physics strict
transitive standard-axiom checks and import-layer checks. Full build passed,
7009 jobs. Both final logs (`/tmp/sm-sparse-focused.log` and
`/tmp/sm-sparse-full.log`) contain no warning/error lines. The failed large
certificate attempt above is recorded separately and is not part of these
successful builds.

The persistent exact diagnostic matched all 19161 known original CSV rows
and all 107 new sparse-output rows (41 positive, 66 zero). The lepton
diagnostic passed 169 exact pairs; exact rational certificate regeneration
matched. Layout passed for 1647 modules. Links passed for 853 Markdown files,
5263 local inline links and 106 heading fragments, zero errors (a later
sandbox `git` subprocess denial was retried read-only with approval). The original
CSV, root README, pins, dependencies and Weyl premise are unchanged.

The final Lean export matched `neutral-sparse-results.csv` byte for byte
(`pipefail` enabled). Diff review and `git diff --check` passed. The final
staged diff is checked before the topic commit. No merge or push is authorized.
