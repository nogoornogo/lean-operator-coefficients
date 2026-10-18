# Rank formulas, bounded recount and computation boundary

## Proved ranks

[SMChargedKernelRank](../../../Physics/StandardModel/Operators/SMChargedKernelRank.lean)
uses exactly `SMFullLocalKernel.constraints`, on its actual statistical
source/Higgs carrier. For all supplied residual flavor representations,
content words p, constituent degrees m and twists delta:

- `local_charge`: nonzero actual local invariants require
  `hypercharge(p) + 3*delta = 0`.
- `full_rank`: if that sum is nonzero, rank equals the number of columns.
  This includes zero-column matrices and adds no positive-dimension premise.
- `dimension_zero_above_cutoff` and `rank_zero_above_cutoff`: for content
  length above 180 the carrier dimension and matrix rank are both zero.

These are exact symbolic rank formulas. Numerical ranks of neutral entries
within the degree bound are still unevaluated; even the column dimension of a
general content is currently expressed with `Module.finrank`.

## Reproduced enumeration

[The script](../../../tools/sm-rank-enumeration/enumerate.py) independently
enumerates all q,l modulo k for k=2,...,12, retaining `3q+l != 0`. It reproduces
649 initial assignments, 572 retained labelled assignments and 151 fixed-order
unit orbits. It reproduces the bounded B2/LLHH profile counts
20/166/70/316 and all effective-order counts. The committed
[CSV](../../../tools/sm-rank-enumeration/candidates.csv) lists all 572 rows,
lexicographically minimal orbit representatives and those bounded properties.
Every run checks the CSV against regenerated rows.

This is a repeat of the existing bounded classification, checked against
`InverseCyclicSMCharges`, `InverseCyclicChargeOrbits` and
`InverseCyclicSectorProperties`. No row asserts all-degree B1 protection.
The external script is not a Lean proof premise.

## Why the all-rank computation does not follow immediately

`SMFullLocalKernel.basis` delegates to `SMWeylFiniteKernel.basis`, which uses
`Module.finBasis` on a statistical image. This basis is classical, not an
executable list of exterior coordinates. The compact tests use `Circle.exp 1`;
the proof of exact exhaustiveness does not provide an executable exact field
backend for those complex entries. Floating-point elimination would not
certify equality of the original complex rank.

The actual `SMFiniteSupportTable.Index` enumerates ordered species words up to
length 180 and two indices of size 181. Its cardinal is

    181^2 * sum(n=0,...,180) 10^n,

approximately `3.64 * 10^184`. Even an occupation-number box capped by the ten
species dimensions has `1,477,408,647,169` entries before gauge/charge filters.
This is a size diagnostic, not a proved implementation of that compression
or a lower bound on surviving entries. The ambient middle exterior space has
dimension `binomial(180,90)`, about `9.10 * 10^52`; it is not a single selected
matrix dimension.

Two continuations were inspected:

1. Direct exact matrices require an executable ordered exterior basis for
   `PatternExteriorSource.Source`, a proved coordinate equivalence, exact
   compact coefficient arithmetic or replacement tests with certified
   exhaustiveness, and certified rank transport. Existing source projection
   and surjectivity proofs alone do not supply that basis. Literal full-table
   materialization is not repository-scale computation.
2. Compressed multiplicity/weight counting could avoid materialization, but
   needs a proved extraction of invariant multiplicities on the actual
   statistical carrier, including the paired Weyl action. The existing
   compact Hom dimension interface does not supply an executable coefficient
   extraction formula for this noncompact local group. No Lie/compact
   replacement is silently assumed.

The scope stop is a new certified computational representation/compression
foundation and the infeasibility of literal exhaustive materialization under
the repository's lightweight computation rule. The finite-kernel equivalence
remains valid. It is not a ready-to-run all-content rank algorithm. A next
bounded milestone should construct executable coordinates and rank transport
for one selected neutral content, then establish a compression theorem before
attempting an all-content calculation.
