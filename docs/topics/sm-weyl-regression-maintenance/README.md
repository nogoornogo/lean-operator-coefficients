# SM Weyl specialization regression maintenance

- Status: completed
- Result type: reproducible external diagnostic and documentation maintenance
- Branch: `audit/sm-weyl-regression-maintenance`
- Integration target: `master`; merge explicitly authorized at stage 01
- Authorization: user requested a separate maintenance topic and script tests.

## Frozen endpoint

Persist a standard-library exact-integer diagnostic for the six-coordinate
SM torus, positive roots and all ten signed three-generation species. Compare
constant-content multiplicities with every certified CSV rank, test neutral
unclassified entries without changing their status, and use independent
small-degree subset enumeration to check the exterior dynamic program.
Check empty/top exterior powers, dimensions and conjugate conventions.
The review's scratch script is absent from this checkout; reconstruct the
diagnostic from linked source conventions rather than claiming to preserve it.

Clarify the table's neutral/nontrivial coverage, link the cutoff checkpoint to
later q/l results, and place the missing/misplaced topic-index entries under
their subject headings. Do not edit the root README or Lean sources, introduce
dependencies, certify new rank rows, or implement the computable Lean character
bridge (a separate topic). Python results are not theorem premises or proofs.

## Source conventions and verification

- [Torus and roots](../../../Physics/StandardModel/Operators/SMCompactTorus.lean)
- [Signed gauge/chirality dictionary](../../../Physics/StandardModel/Operators/DeltaLOneSignedFields.lean)
- [Integral hypercharges](../../../Physics/StandardModel/Operators/DeltaLOneSignedInput.lean)
- [Actual combined compact action](../../../Physics/StandardModel/Operators/SMCombinedCompactAction.lean)
- [Certified constant ranks](../../../Physics/StandardModel/Operators/SMConstantContentRanks.lean)
- [Tool documentation](../../../tools/exact-rank/README.md)

Acceptance: exact regression script, existing lepton diagnostics and certificate
regeneration, layout/link/diff checks, diff review and coherent commit. No Lean
build/axiom audit is required when Lean sources and inputs remain unchanged;
this creates no new proof baseline. Record actual outcomes below at completion.

## Result and verification

Implemented `tools/exact-rank/check-sm-weyl.py` with grouped exact exterior
weight DP, homogeneous hypercharge, inverse-character root extraction and
independent small-degree subset checks. All ten species and all 19161 certified
CSV rows match. The 107 unclassified rows give diagnostic values 41 positive /
66 zero; their certified status and the CSV remain unchanged. LLHH/conjugate
LLHH, DUQL flavor count, independent-spin exclusion and Q upper-degree controls
pass. This diagnostic does not prove a weight presentation or extraction law.

The assumptions ledger now distinguishes the 19160 structural full-rank rows
from the one certified neutral LLHH row (1/108 neutral even-degree entries).
The cutoff result links its successor q/l extraction. The seven misplaced
index entries were moved to Physics/GUT headings, and SU(6) light-placement
search was added; its search-class boundary is preserved.

Executed successfully:

    python3 tools/exact-rank/check-sm-weyl.py
    python3 tools/exact-rank/check-lepton-weights.py
    python3 tools/exact-rank/certify.py tools/exact-rank/examples.json --check Math/LinearAlgebra/ExactRankCertificateExamples.lean
    node tools/layout/check-layout.mjs
    node tools/docs/check-links.mjs
    git diff --check
    git diff --cached --check

The lepton diagnostic passed 169 exact pairs; certificate regeneration matched.
Layout passed for 1633 modules. Links passed for 846 Markdown files, 5232 local
links and 106 heading fragments, zero errors; the unchanged read-only checker
used its approved sandbox-subprocess retry. Diff checks passed. Lean sources,
theorem premises, CSVs and dependency pins are unchanged: no Lean build or axiom
audit was rerun and no new proof baseline is claimed. No merge or push occurred.

## Master integration

Topic tip `checkpoint 01` was merged without conflicts as `checkpoint 02`, from master
`checkpoint 03`, using `git merge --no-ff audit/sm-weyl-regression-maintenance`.
The exact Weyl diagnostic, lepton diagnostic, certificate regeneration,
layout and link checks above were rerun successfully on the merged state;
links retained the recorded 846/5232/106 counts. Diff checks passed. No Lean
source or premise changed, so no Lean build/axiom audit was rerun. The local
topic branch was safely deleted after reachability and worktree checks.
No remote push occurred.
