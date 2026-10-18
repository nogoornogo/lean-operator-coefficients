# Computable character verification

This records the reference checkpoint `checkpoint 01`.
[Sparse continuation verification](sparse-verification.md) records the later
proved optimization, all-107 execution and remaining arithmetic boundary.

Verification passed for the uniform computable presentation and
conditional support endpoint. The reference term-list representation replaces
the proposed executable Finsupp API because the fixed library uses classical
finite-support operations. This changes no theorem premise or model input.

Executed checks:

    lake build Math.RepresentationTheory.Audit.AuditComputableWeightPolynomial Physics.StandardModel.Operators.Audit.AuditSMComputableCharacter
    lake build
    python3 tools/exact-rank/check-sm-weyl.py
    python3 tools/exact-rank/check-lepton-weights.py
    python3 tools/exact-rank/certify.py tools/exact-rank/examples.json --check Math/LinearAlgebra/ExactRankCertificateExamples.lean
    node tools/layout/check-layout.mjs
    node tools/docs/check-links.mjs
    git diff --check
    git diff --cached --check

Arithmetic controls use `decide +kernel`, with no changed resource flags or
native reduction axioms. The computational boundary is the reference
binomial-size exterior term list; billion-term constant-Q evaluations are not
attempted. No unconditional CSV value or physical input is changed.

Focused build passed, 4420 jobs, including 15 Math and 40 Physics strict
transitive standard-axiom checks and import-layer checks. Full build passed,
7002 jobs. Final `/tmp/sm-computable-focused.log` and
`/tmp/sm-computable-full.log` have no warning/error lines. Early elaboration
and integer-to-Nat normalization failures were corrected; no flags, premises
or audits were weakened. The persistent examples include 11 kernel-checked
integer/Boolean evaluations, a content-count identity and the conditional L4
kernel/rank consequences. The standalone executable probe returned 6, 6 and
true for LLHH, conjugate LLHH and the neutral q/l test.

The exact Weyl diagnostic reproduced all 19161 certified CSV rows and the
107 diagnostic values (41 positive, 66 zero). Lepton diagnostics passed 169
exact pairs; exact rational certificate regeneration matched. Layout passed
for 1640 modules. Final links passed for 850 Markdown files, 5251 local links
and 106 fragments, zero errors (approved read-only sandbox-subprocess retry).
Diff checks passed. Dependency pins, the original CSV, root README and the
Weyl literature premise are unchanged. No merge or push occurred.

The primary uniform presentation and conditional support endpoint is complete.
The all-107 numerical extension stops at the lightweight-computation boundary:
the proved reference list length is binomial, reaching over nine billion terms
for Q middle degree. No such materialization was attempted. Efficient sparse
aggregation/degree-table refinements and all-target q/l search remain unproved
extensions, not missing hypotheses of the completed endpoint.
