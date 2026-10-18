# Arbitrary Selectors on Diagonal Cyclic Dipole Modules

For any positive cyclic order and finite diagonal flavor modules with charges
a_i and b_j, actual selected B/W dipole allowance is equivalent to

    exists i,j: a_i=b_j, mu_i != 0, ell(e_j) != 0.

Here mu is an arbitrary source vector and ell an arbitrary target linear
functional. Selected prohibition is the negation. Both zero-selector controls
are proved, and empty index sets are allowed. No semisimplicity hypothesis or
surjectivity of a generated-coefficient map is added.

The proof first derives zero matrix entries between unequal charges using the
previous faithful cyclic character criterion. It expands ell(f(mu)) as a finite
double sum. A nonzero evaluation requires a supported matching pair; conversely
its equivariant matrix unit has nonzero evaluation. Independent B/W channels
are connected through the existing actual coefficient equivalence.

The [source](../../../Physics/StandardModel/Operators/CyclicSelectorDipoleSelection.lean)
contains SupportedMatch, coordinate_zero, evaluation_expand,
selected_allowed_iff, selected_forbidden_iff and zero-selector controls.
The [contract](lfv-contract.md) is complete. This is more general than the
previous basis-selector theorem, but remains diagonal cyclic. Arbitrary
nonabelian actions retain the existing exact intertwiner-evaluation criterion;
weight overlap alone ignores selector support. No physical rate is claimed.
