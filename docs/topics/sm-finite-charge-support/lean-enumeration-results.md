# Lean-owned enumeration and aggregate certification

## Proof path

The intermediate literal table and Python table renderer are removed from
the active proof path. `SMFiniteLeptonAssignments.candidatePairs k` takes
the product of two natural representative ranges, then filters only by
`(3*q+l)%k≠0`. Eleven batches cover k=2,…,12. `classify` calculates both
verdicts using the already-proved finite lepton-charge criterion. No CSV,
external expected row, Python execution or input count defines these objects.

`all_correct` now follows symbolically from these definitions and the general
support theorem, rather than checking externally proposed flags. The ordinary
library build checks the entire path.

## Exact closed obligations

| Obligation | Lean declaration |
| --- | --- |
| Exact candidate membership, both directions | `mem_keys`, `mem_rows_key` |
| No repeated assignment triple | `keys_nodup` |
| Each admissible triple occurs exactly once | `unique_coverage` |
| Connection to the actual computed rows | `keys_eq`, `rows_nodup` |
| Total is 572 | `row_count`, `rows_length`, `keys_length` |
| Four class counts are 326/144/102/0 | `partition_counts` |
| Counts are filters of the complete row list | `classCount_rows` |
| B1 allowed/forbidden totals are 326/246 | `b1_allowed_count`, `b1_forbidden_count` |
| B2 allowed/forbidden totals are 470/102 | `b2_allowed_count`, `b2_forbidden_count` |
| Classes mean actual original-space allowance/prohibition | `class_iff` |

All count equalities are checked in the Lean kernel; no native_decide,
custom axiom, external table premise or changed proof option is used.
Uniqueness and completeness are symbolic list/range proofs. Closed counts
use `decide +kernel` on small bounded definitions; no raw operator-support
or generation-occupation search is repeated. The count theorem includes the
fourth class (B1 allowed/B2 forbidden) being empty within this domain, without
claiming that class is impossible for arbitrary k.

## Optional CSV export

`export-assignments.py` runs the retained Lean export template. Its input is
the Lean-owned definitions and its output is CSV. It reads no CSV by default;
`--compare` is a separate external regression option. The exported verdicts
and displayed minimum-|L| choices match the old CSV byte-for-byte. Those
display choices are not a minimum-engineering-dimension theorem.

The old CSV and 1716 generated original-space certificates remain reproducible
checkpoint evidence, not proof prerequisites. The opt-in verifier checks the
witness renderer, the persistent audit, the new Lean export and the older
independent proof/degree certificates. It cannot recreate or overwrite the
hand-maintained Lean assignment definitions using an external renderer.

## Verification and failure accounting

Focused final source/examples/audit build passes: **14.8 s**, sampled group
peak **5782344 KiB** (about 5.51 GiB), **1199 strict transitive checks**,
zero warnings/errors. The assignment module itself took 6.9 s with cached
imports. The optional Lean export passes: 6.5 s, 5101296 KiB, exact historical
CSV agreement. All use the fixed one-thread/300 s/10 GiB/4 GiB reserve guards.
No resource stop or computational explosion occurred.

Development failures are not accepted evidence: first definition build
(5.8 s, 5246488 KiB) had an implicit argument, a simplification mismatch and
parser spacing errors; those were corrected using the source APIs. A second
bounded pass (8.5 s, 5776244 KiB) needed the correct count lemma name; the
next pass (8.0 s, 5776212 KiB) corrected its namespace and removed a nonexistent
Bool lemma. The intermediate complete build passed (14.0 s, 5779456 KiB,
1193 strict checks). The first optional export (6.2 s, 5082044 KiB) needed an
explicit Int binder before evaluation. The final accepted results above
contain the corrections. No failed file or recovery placeholder is accepted
by the strict audit, and no limit or dependency was changed.

The updated independent regression target passes in full, including optional
Lean export/historical CSV equality, original certificates (67.0 s,
7019808 KiB, 3724 strict checks), and all 796 degree bounds (85.2 s,
7025940 KiB, 2812 strict checks). The original certificate source identity
and verdicts are unchanged. These external comparisons supplement the
Lean-owned proofs; the normal library build needs none of their CSV files.

The full default-root `lake build GUT` passes **7342 jobs**, zero
warnings/errors, 8.5 s, 6708140 KiB sampled group peak. Layout passes 1956
modules; local links, diff checks and Python syntax checks pass. The
[machine-readable evidence](lean-enumeration-verification.json) records the
current source hashes and measurements. Final documentation-only completion
edits do not change this Lean baseline and require no further Lean build.

This closes the enumeration/count endpoint on the existing
`proof/sm-finite-charge-support`. No master merge, push, root README edit,
dependency/proof-limit change or new physics scope was introduced. Minimum
engineering dimension and rates remain outside the proved claim.
