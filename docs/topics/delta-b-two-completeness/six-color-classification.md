# Six-color classification by pair partitions

## Statement and scope

Let `V = Fin 3 → ℂ` carry the defining action of `SU(3)`. Every invariant
complex multilinear functional on six copies of `V` is a unique linear
combination of the five products of determinant tensors with slot partitions

`(012)(345)`, `(013)(245)`, `(014)(235)`, `(023)(145)`, `(024)(135)`.

The source is [SixColorInvariant.lean](../../../Physics/StandardModel/Gauge/SixColorInvariant.lean).
The result concerns arbitrary six-color invariants before imposing species
alternation or combining color with Weyl indices. It has no literature premise.

## Readable proof structure

1. **Weights.** Three diagonal special-unitary matrices with entries `-1, i, i`
   force every nonzero basis coordinate to have each color occur twice.
   A color occurring `k` times has multiplier `-i^k`; the multiplier can be one
   only for `k = 2` or `6`. A nonbalanced six-tuple has at least one color with
   neither multiplicity. This proves `basisValue_vanish`.
2. **Color names.** A color transposition multiplied by the scalar `-1` lies
   in `SU(3)`. Its six signs cancel. Thus exchanging color names preserves
   every coordinate (`basisValue_swap`, `basisValue_relabel`). A balanced tuple
   therefore describes a partition of six positions into three unordered pairs.
   There are `5 × 3 × 1 = 15` such partitions, represented by assigning color
   names in order of first occurrence.
3. **One relation.** Apply the real rotation with cosine `3/5` and sine `4/5`
   in the 0–1 plane to the tuple `000122`. Multilinearity expands its four active
   positions. Unbalanced terms vanish; color exchanges identify complementary
   assignments. The remaining coefficient is `84/625`, which is nonzero.
   Consequently

   `x(001122) + x(010122) + x(011022) = 0`.

   The generic `rotation_expand` supplies the expansion once. Reordering slots
   gives the same three-term relation for any spectator pair
   (`three_term_permuted`).
4. **Five probes.** Use `001122`, `001212`, `010122`, `010212`, `012012`.
   Ten applications of the preceding relation determine every other pair
   partition. Each application is a sum of three representative values, with
   coefficients one. No elimination certificate or rank assertion is assumed.
   With five zero probes, all coordinates vanish, and basis extensionality
   proves that the multilinear map itself is zero (`eq_zero_of_probes`).
5. **Reconstruction.** The five epsilon products are multilinear and invariant
   by determinant invariance. Their probe evaluation matrix is triangular:
   four probes read single coefficients, while `012012` reads `c₀ + c₄`.
   The inverse coordinates are therefore

   `(x(012012)-x(001122), x(010212), x(010122), x(001212), x(001122))`.

   Subtract this reconstruction from an arbitrary invariant map and apply the
   zero-probe theorem. This proves spanning and uniqueness together.

## The ten relations

The tuple names below are the canonical pair-partition representatives.
Each row has the same equation `x(a) + x(b) + x(c) = 0`; the determined value
has only the other two values as dependencies.

| Spectator positions | Three representatives | Newly determined |
| --- | --- | --- |
| 0, 1 | 001122, 001212, 001221 | 001221 |
| 0, 2 | 010122, 010212, 010221 | 010221 |
| 1, 4 | 010212, 012012, 012210 | 012210 |
| 2, 3 | 001122, 012201, 012210 | 012201 |
| 1, 5 | 010221, 012021, 012201 | 012021 |
| 0, 3 | 011022, 012012, 012021 | 011022 |
| 2, 4 | 001212, 012021, 012120 | 012120 |
| 0, 5 | 011220, 012120, 012210 | 011220 |
| 1, 2 | 011022, 011202, 011220 | 011202 |
| 0, 4 | 011202, 012102, 012201 | 012102 |

## Finite-check boundary and API

`decide +kernel` is used for finite combinatorial facts: color-count coverage,
coverage by the fifteen representatives, bijectivity of slot orders, and
correspondence between the slot/color relabelings and the stated triples.
These checks contain no arbitrary complex coefficient values. Relations
between those values follow from group invariance and multilinearity.

The API provides `reconstruct`, `coordinates`, both inverse identities,
`existsUnique_pairing_coordinates`, spanning on arbitrary input vectors through
`exists_pairing_coordinates`, invariant equality via `eq_of_coordinates`,
`linearIndependent_pairing`, and `invariantEquiv` for the intrinsic invariant
space. The proof uses the default heartbeat and recursion limits.

The earlier 85-step coordinate elimination implementation was rejected and
replaced. It is not a proof baseline or a dependency of this construction.
