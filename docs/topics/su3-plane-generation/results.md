# Actual Three-Plane SU(3) Decomposition

## Proved endpoint

[PlaneGenerationThree](../../../Math/LieGroups/SpecialUnitary/PlaneGenerationThree.lean)
works with the actual `Matrix.specialUnitaryGroup (Fin 3) ℂ`, with no
additional generation, continuity, literature or complexification premise.

`planes` is the family of actual SU(3) matrices fixing one coordinate basis
vector. Unitarity also fixes that coordinate row (`row_fixed`), so this is a
two-coordinate unitary family with determinant one, not an arbitrary family
of all group elements. `tail_mem` proves explicitly that an element fixing
the first coordinate has an actual SU(2) lower-right block.

`matrix01` and `matrix02` embed the normalized complex two-coordinate form

    [ a          b      ]
    [ -conj(b)   conj(a)]

in the 01 and 02 coordinate planes. `matrix01_mem` / `matrix02_mem` prove
unitarity and determinant one from `a*conj(a)+b*conj(b)=1`.
`eliminate_pair` constructs normalized coefficients annihilating a pair's
second coordinate. Its zero-pair branch is the identity; the other branch
uses the positive exact square root of `normSq(x)+normSq(y)`.

`reduce_first_column` applies a 01 rotation to kill the second coordinate of
an arbitrary SU(3) first column. Column unitarity then gives a normalized
remaining 02 pair, and a second rotation takes that column exactly to the
first standard basis vector. The residual matrix lies in `planes`.

`inverse_plane` shows inverses stay in this family.
`three_plane_decomposition` proves that every actual SU(3) element is a
product of three actual plane elements. Thus `closure_planes` and
`generates` prove **algebraic subgroup closure**, not merely topological
density. `invariant_iff` then proves that testing the plane family is
exhaustive for invariant functionals in any complex representation of this
actual SU(3) group. No irreducibility or Lie integration premise is used.

## Boundary

The parameter family remains infinite. This theorem does not prove that
finitely many chosen SU(2) parameters test every statistical SM source.
Explicit bounded-degree parameter identities, suitable exact sampling and
statistical image/quotient descent are still needed for the parent finite
matrix endpoint. No full support classification or numerical rank enumeration
is claimed. The next milestone can test these constructions on one nontrivial
statistical source before a general content adapter is attempted.

The later [compact-kernel result](../sm-compact-kernel-completion/results.md)
uses fixed circle factors instead of rational parameter interpolation and
closes this finite-sampling boundary for every retained statistical content.

This topic's frozen SU(3) generation endpoint is achieved; no new foundation
or scope-change stop was encountered. The parent SM matrix connection was
still open at this checkpoint and is closed by the later result linked above.
No merge or push is included in this checkpoint.
