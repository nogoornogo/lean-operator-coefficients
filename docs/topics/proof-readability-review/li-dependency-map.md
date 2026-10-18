# Li six-quark dependency map and first structural split

This is an earlier partial checkpoint. The completed Li source/orbit
replacement is recorded in [the current result](source-replacement-results.md)
and [its verification](source-replacement-verification.md).

## Meaning of the data

The independent local array has two indices of size five. The first indexes
color invariant coordinates and the second spin invariant coordinates; flattening
uses `finProdFinEquiv` on their product. Columns of `basisRational` are the 25
selected orbit vectors in these coordinates, not 25 flavor-independent operators.
`selectedSeed` and `selectedWord` specify the seed and ordered within-species
exchanges for each column. The last column is the separately added seed.

`LiSixQuarkFiniteData` contains several different obligations:

- `rationalCoordinates` derives seed coordinates from epsilon contractions,
  48 weighted permutations, normalization and independent color/spin probes.
- `rationalSeedCoordinates` is a cached 11-by-5-by-5 table. Its agreement with
  that derivation is checked by `rationalCoordinates_eq`.
- `basisRational` caches the 25 selected orbit columns. In `LiSixQuarkOrbitData`,
  `step_checked` and `orbit_column` connect successive exchange actions to them.
- `inverseRational` supplies a dense coordinate extraction matrix. Its two
  product identities are closed rational calculations.

`LiSixQuarkConvention.candidate_coordinates` connects the literal candidate to
these seed coordinates. `LiSixQuarkCertificate.orbitArray_agrees` connects
semantic orbit arrays to matrix columns. `matrixEquiv` and `coordinateEquiv`
then use both inverse products. `LiSixQuarkLocalBasis` transports this to
independence, reconstruction and actual invariant coefficients. Residual and
flavor consumers build on those equivalences.

## Circularity check

`LiSixQuarkPrintedSpan.printedSpan_eq_kernel` reconstructs every array using
`coordinateEquiv`. Thus its reverse inclusion already depends on the dense
inverse. `printed_finrank` uses that equality. Neither result is an independent
24-dimensional spanning proof that can simply replace the inverse calculation.

By contrast, `LiSixQuarkExtension` imports neither finite data nor orbit tables.
Its explicit `extra` and normalized `extraProbe` have readable small formulas.
Their normalization and exchange properties still use small coordinate arithmetic;
this is not a claim that all computation disappears from their ancestry.

## Frozen pilot and result

For the independently defined local array and normalized probe, set

$$
P(c)=\mathrm{extraProbe}(c),\quad e=\mathrm{extra},\quad
c_0=c-P(c)e.
$$

Since $P(e)=1$, $P(c_0)=0$ and $c=c_0+P(c)e$. If $c=k+ze$ with $P(k)=0$,
applying $P$ gives $z=P(c)$ and subtraction gives $k=c_0$. These arguments
supply an explicit linear equivalence

$$
V\simeq\ker P\times\mathbb C.
$$

The pilot in `LiSixQuarkProbeDecomposition` freezes exactly this splitting,
its uniqueness and the kernel dimension. It uses linearity and normalization,
not the selected 25-vector basis, dense inverse, or a new representation theorem.
The new audit rejects imports of the dense finite-data and basis modules.

This is a genuine spanning and uniqueness statement for a hyperplane plus its
complementary line. It does **not** establish that the ten printed orbit families
span that hyperplane. The downstream dimension proof can reuse the independent
kernel-dimension theorem while retaining its separately proved span equality.

## Remaining replacement obligation

To remove the dense inverse from the full Li theorem, construct the kernel
from printed orbits without `coordinateEquiv`: either an explicit sequence of
small invariant blocks with reconstruction, or a direct symbolic elimination
whose steps explain the chosen contractions. Deriving a table by evaluation
or using the old printed-span equality would not meet this obligation.

Before extending the pilot, inspect whether the existing color/spin actions
admit such small blocks. If the only available route requires a new general
representation decomposition, record that missing interface and stop as planned.

## Existing interfaces and scope boundary

The existing `SixQuarkInvariant` reconstructs the independent 5-by-5 local
coordinates from color and Weyl pairings. `SixQuarkSpeciesQuotient` proves the
four generator actions by symbolic epsilon identities. These provide the
carrier and its action, but not an independent block reconstruction of the
24-dimensional probe kernel by the selected printed orbits.

The exact missing interface is: for every `c` with `extraProbe c = 0`, construct
coefficients of the first 24 selected literal orbit arrays whose sum is `c`,
without using `matrixEquiv`, `coordinateEquiv`, `inverseRational`, or an equivalent
closed 24-by-24 elimination certificate. The existing reverse inclusion of
`printedSpan_eq_kernel` cannot supply this interface without circularity.
A representation-theoretic replacement would need a new block decomposition
of the restricted color/spin product and seed projections onto those blocks;
that construction is not supplied by the existing six-quark APIs inspected here.
No impossibility of a more elementary symbolic derivation is claimed.

## Bounded verification stop and retained change

A direct rewrite of `LiSixQuarkFiniteData.rational_right_inverse` was attempted:
for finite square matrices, the generic `mul_eq_one_comm` theorem derives it
from `rational_left_inverse`. The general theorem was checked independently.
However, checking the entire changed finite-data file re-evaluated its retained
closed numerical proofs and hit the 10 GiB sampled process-group guard. The
runner stopped after 110.3 seconds at 10,492,236 KiB. No theorem failure was
reported; no resource limit was increased. That file change was reverted.

The same mathematical simplification is retained at the consumer boundary:
`LiSixQuarkCertificate.right_inverse` now follows directly from `left_inverse`
by the general finite-square-matrix theorem. Its proof no longer calls
`rational_right_inverse`. The original rational right-inverse declaration is
still present in the unchanged finite-data file and is **not retired**.

This is the plan's bounded resource stop for a full numerical-file rewrite.
The independent probe split and the consumer simplification remain the bounded
verified milestone. The 25-by-25 tables, the left-inverse calculation, seed
coordinate calculations and orbit checks are not claimed replaced. Work on
Heeck–Le, SU(6), rank examples and E6 has not started in this milestone.
