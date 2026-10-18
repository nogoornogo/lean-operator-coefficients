# Reassessment of the 572 assignments

## Fixed target

The [contract](assignment-plan.md) extends the earlier feasibility checks at
explicit user request. The domain is the unchanged original CSV: all
`2 ≤ k ≤ 12`, `q,l : ZMod k`, `3q+l ≠ 0`. It has 572 assignments and 151
unit orbits. The older bounded B2/LLHH flags remain unchanged and retain
their earlier meaning.

The new checks use actual `SMQLPatternRequests.OriginalAllowed` and
`OriginalForbidden`, over every signed content and arbitrary Higgs bidegree.
B1 means absolute integer three-baryon charge 3, B2 means 6.
The fixed three-generation SM dictionary, independent Lorentz action,
residual-neutral Higgs and scalar cyclic q/l action are unchanged.

## Partition

| Actual all-degree result | Assignments | Unit orbits |
| --- | ---: | ---: |
| B1 allowed, B2 allowed | 326 | 69 |
| B1 forbidden, B2 allowed | 144 | 56 |
| B1 forbidden, B2 forbidden | 102 | 26 |
| Unknown | 0 | 0 |

Thus 246 assignments forbid B1, 470 allow B2, and exactly 144 satisfy
`SMQLPatternRequests.b1ForbiddenB2Allowed`. The 572 count was a bounded
candidate count, not the count of all-degree B1 protections.

| k | Candidates | B1 forbidden | B2 forbidden | B1 forbidden/B2 allowed |
| --- | ---: | ---: | ---: | ---: |
| 2 | 2 | 2 | 0 | 2 |
| 3 | 6 | 0 | 0 | 0 |
| 4 | 12 | 10 | 4 | 6 |
| 5 | 20 | 4 | 4 | 0 |
| 6 | 30 | 18 | 0 | 18 |
| 7 | 42 | 6 | 6 | 0 |
| 8 | 56 | 42 | 20 | 22 |
| 9 | 72 | 6 | 6 | 0 |
| 10 | 90 | 58 | 16 | 42 |
| 11 | 110 | 10 | 10 | 0 |
| 12 | 132 | 90 | 36 | 54 |

The [572-row output](../../../tools/structural-support/results/assignment-verdicts.csv)
records separate B1/B2 results, a selected lepton-charge witness for each
allowance, and the combined request. An allowed coefficient is not a generated
interaction, UV realization or rate.

## Degree interpretation

These are existence/prohibition decisions across all degrees. They do not
determine the minimum engineering dimension or assert allowance at dimension
six. The following minimum attainable absolute lepton charges are now
kernel-proved by `SMFiniteLeptonDegreeBounds.minimum_distributions` in the
ordinary library build; they agree with the earlier selected witnesses:

| Absolute L | B1 allowed rows | B2 allowed rows |
| --- | ---: | ---: |
| 0 | 0 | 186 |
| 1 | 48 | 0 |
| 2 | 0 | 72 |
| 3 | 160 | 0 |
| 4 | 0 | 80 |
| 5 | 44 | 0 |
| 6 | 0 | 92 |
| 7 | 26 | 0 |
| 8 | 0 | 20 |
| 9 | 38 | 0 |
| 10 | 0 | 20 |
| 11 | 10 | 0 |

The uniform minimum theorem covers the entire proved finite charge range
for arbitrary nonzero k,q,l, not just a diagnostic candidate range. Smaller
|L| is excluded for every actual allowed content, including negative B3.
In particular, the 278 B1 rows with minimum |L|≥3 exclude all |L|=1 contents.
Every allowed B1 content in those
rows must have at least six fermions and engineering dimension at least nine.
The 284 B2 rows with minimum |L|≥2 similarly require at least eight fermions
and dimension at least twelve. `high_degree_counts`, `high_row_bounds` and
the row-bound interfaces prove those counts and implications in the default
build. All 796 allowed row/target applications are covered without generated
arithmetic-gate premises; None represents prohibition.

The general count inequality is `|B3|+|L|≤n`. With engineering dimension
`D=3*n/2+h+d`, scalar factors can only increase D. Neither this inequality
nor minimizing |L| proves that the dimension lower bound is attained: quark
pairs, statistics, joint support and required Higgs factors also matter.
The [maintenance topic](../sm-finite-charge-support/README.md) owns the new
Lean lower-bound interfaces and the opt-in regression target. The original
verification measurements below remain evidence for their original checkpoint.

## Why an all-degree decision is possible here

For any nonzero local coefficient, total fermion degree is even by
`SMParityKernelRank.forbidden`. Existing
`InverseLeptonParitySelection.content_parity` then makes B+L even, where B
is integer three-baryon charge. Residual charge is exactly `B*q+L*l`.
The diagnostic `parityExclusion` bridge proves actual original-space
prohibition when these conditions cannot be simultaneously neutral.
For every forbidden row the kernel discharges the universal integer arithmetic
gate using `omega`; it does not enumerate all contents or Higgs degrees.
No exterior-capacity bound or Weyl multiplicity law is assumed.

For each remaining row, a small finite witness family is enough. B1 uses
L=±1,±3,±5,±7,±9,±11; B2 uses L=0,±2,±4,±6,±8,±10.
For each of these 23 families, balanced generation occupations and an explicit
first live component are proposed, and the full joint color/weak/left/right
support is checked in the kernel. Pattern counts, hypercharge, admissibility
and the B/L selector are checked independently, then `original_ql_iff`
transports the result to an actual coefficient space. Each closed assignment
must separately prove residual neutrality. A missing or invalid witness would
fail verification; absence of a witness is never used to prove prohibition.

Finally, every assignment has its own theorem for the actual combined request,
using `b1_b2_original_iff`. The external gcd test only selects candidate proof
shapes. It is checked against a full arithmetic period `2k` and unit actions,
and is never a theorem premise. All assertions are fixed-domain results for
these 572 assignments; no universal closed support formula or generic compiled
evaluator is claimed.

## Reproduction and verification

The retained [generator](../../../tools/structural-support/assignment-certificates.py)
and [parity bridge](../../../tools/structural-support/probes/assignment-parity-bridge.lean.txt)
use the existing occupation-witness bridge. Exact commands are in the
[tool README](../../../tools/structural-support/README.md#572-assignment-certificates).
The final generated file audits every local declaration transitively, allowing
only `propext`, `Classical.choice`, and `Quot.sound`.

The complete guarded run passed in **87.9 seconds**, with sampled group peak
**6941656 KiB** (about **6.62 GiB**), no warnings/errors and **3724 strict
transitive local declaration checks**. All 1716 assignment theorems and 23
original-space witness bridges were present. No resource guard was hit.
The preceding 23-family transport check also passed: 25.3 seconds,
5466980 KiB (about 5.21 GiB). Limits were 300 seconds per run, 10 GiB sampled
RSS and 4 GiB host reserve, with one Lean thread and unchanged proof options.

Accepted generated-source SHA256:
`9ec32decd430d29b6aac3fdf83fa33df2fccab9ca65d8a494e373568297fcd0b`.
The original candidate CSV SHA256 is
`2e54112947c0fdb955d3ba90425d024100acab92a9a7735b8db30a49b26f933b`.
[Machine-readable evidence](../../../tools/structural-support/results/assignment-summary.json)
records counts, resource measurements and script/template/output hashes.

An initial full proposal failed because admissibility had no registered
`Decidable` instance (44.9 s, 6440376 KiB); the strict audit rejected the
resulting elaboration placeholders. A subsequent arithmetic attempt was
stopped after diagnostics showed an unreduced finite-index value. Explicitly
changing to the closed admissibility target and proving its inequalities
corrected the transport. Neither failed attempt is an accepted proof baseline;
no proof limit was raised and no custom axiom or source `sorry` was added.

The original candidate recount, independent period/unit-action controls,
23 witness charge/hypercharge dictionaries, exact generated-table comparison,
Python syntax and generated-target/token checks pass. Layout remains 1939
modules; documentation links and diff checks pass. No active library `.lean`
source/import/dependency changed, so no new full library build was rerun;
the earlier successful 7325-job baseline remains the library baseline.
This is reproducible kernel-certified diagnostic coverage, not a new compiled
library API. The previously completed 107-row sign checks and observed raw
runtime failures retain their separate evidence. No rewrite, merge or push.
