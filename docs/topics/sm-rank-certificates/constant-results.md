# Numerical continuation: constant contents and all-content parity

## Proved numerical ranks

[SMConstantContentRanks](../../../Physics/StandardModel/Operators/SMConstantContentRanks.lean)
constructs the numerical dimension formula for every constant species word,
at arbitrary n and Higgs constituent degree m:

    columns = choose(dimension(species), n) * (m+1).

The ten species dimensions are `36,18,18,12,6,36,18,18,12,6`.
`source_dimension` uses the existing constant-pattern exterior equivalence;
`carrier_dimension` adds the symmetric Higgs factor. These are the actual
statistical carrier dimensions, not dimensions before fermion statistics.
`above_capacity_rank` proves rank zero whenever n exceeds species capacity.
`charged_rank` proves that hypercharge mismatch gives the displayed full rank.
The dimension, capacity and charged-rank theorems allow arbitrary supplied
residual flavor representations.

[SMParityKernelRank](../../../Physics/StandardModel/Operators/SMParityKernelRank.lean)
also proves full rank for **every** species content with odd total fermion
degree, with arbitrary m and delta. It uses the actual paired Weyl action:
minus identity acts by -1 on both chiralities, hence by `(-1)^n` on the source;
Higgs constituents are fixed. No replacement by independent chiral groups is
assumed. For mixed contents this is still a full-rank formula; the numerical
column dimension is not yet evaluated generally.

## Exported partial table

The executable classifier `evaluate` returns an optional natural number.
`evaluate_sound` proves that every successful result equals the rank of
`SMFullLocalKernel.constraints` for `LLHHKernelRank.flavor`, i.e. three flavors
and trivial residual group. Its rules are capacity, odd total degree,
hypercharge mismatch, and the previously proved neutral LLHH rank 192.
Every unhandled entry returns `none`. No completeness theorem for the
classifier is asserted.

[The CSV](../../../tools/exact-rank/constant-content-ranks.csv) is emitted
directly by [Lean code](../../../tools/exact-rank/constant-content-table.lean),
without a Python reimplementation of the classifier. It covers all ten
constant-species contents with `1 <= n <= species dimension`,
`0 <= m <= n*doubletCount(species)`, and `delta=m,m-2,...,-m`. These are the
corresponding finite Higgs-reduction candidate indices.

| Status | Entries |
| --- | ---: |
| Odd-degree full rank | 9226 |
| Hypercharge-incompatible full rank (after parity) | 9934 |
| Neutral LLHH rank 192 | 1 |
| Neutral, unclassified | 107 |
| Total | 19268 |

Thus 19161 entries have certified numerical ranks. The largest carrier in
this table has 172427570700 columns; none of its dense matrices is materialized.
The exporter evaluates proved dimension/rank formulas. Entries beyond species
capacity have rank zero by theorem and are not stored individually.

## Remaining all-content task

This is numerical progress on a precisely specified subset of the full
content universe. The 107 unknown rows are only the remaining neutral rows
of this constant-species table, not all remaining SM contents. Mixed-species
occupation vectors and the empty content are excluded from this CSV.
No q/l residual selection or 572-assignment reclassification is inferred.

The current exact certificate bridge still requires a coefficient/kernel
equivalence for each computation. It supplies no such equivalence uniformly
for mixed contents, and the permutation theorem removes ordering redundancy
without supplying mixed-content dimensions or invariant multiplicities.
Closing the 107 neutral rows likewise needs additional invariant-dimension
proofs; hypercharge neutrality alone is insufficient. The agreed numerical
continuation stops at that missing structural bridge, not at an arbitrary
number of processed entries. All-content numerical classification remains
open. No brute-force expansion of the enormous mixed-content box is attempted.

The [subsequent literature assessment](neutral-literature-plan.md) separates
these prerequisites: closing the 107 constant-content rows does not require
the general mixed-content bridge. Their column dimensions are already known;
the missing input is their invariant multiplicity.
