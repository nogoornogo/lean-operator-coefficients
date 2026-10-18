# Actual color/weak slices for Q degree five

Continuation from `checkpoint 01` on `proof/sm-computable-characters`, integration
target `master`; no merge or push authorized. See the
[completion plan](colored-support-completion-plan.md).

Let A=C tensor W be the actual six-dimensional color/weak gauge factor.
Write C* for dual color, H12 for the previously constructed symmetric-square
contraction kernel on C*, and H31 for the new cubic contraction kernel on C.
In a row below, `(color, w)` means color tensor `Sym^w W`.

The three actual retained representations constructed in `ColorWeakFifthSlices`
are the following positive sums. No multiplicity value or irreducibility of
the harmonic kernels is assumed.

| Proposed independent spin degree | Color/weak retained factors |
|---|---|
| 5 | (C*,1) |
| 3 | (Sym^2 C,3), (C*,3), (Sym^2 C,1), (C*,1), (H12,1) |
| 1 | (C*,5), (C*,3), (C*,1), (Sym^2 C,3), (Sym^2 C,1), (H12,3), (H12,1), (H31,1) |

Calling these representations B5, B3, B1, the proved actual equivalences are

```text
Lambda^5 A tensor Lambda^0 A = B5
Lambda^4 A tensor Lambda^1 A = B3 + B5
Lambda^3 A tensor Lambda^2 A = B1 + (B3 + B5).
```

These are the nonnegative spin-weight spaces of the fifth Q exterior power
by the [uniform exterior slice theorem](exterior-weight-slice-results.md).
Every map preserves the complete SU3 x weak-SU2 action. Source expansion uses
the [middle-color products](colored-middle-products-results.md), the proved
Clebsch-Gordan theorem, and explicit regrouping/inverse maps.

`ColorWeakMiddleGauge` also constructs the actual gauge exterior branches,
their finite analytic models and their continuity and torus bounds.
`DoubletMiddleProducts` supplies complete small weak products for degrees
five/six from uniform Clebsch-Gordan, including repeated retained factors.

This checkpoint does not yet assert the full fifth exterior decomposition:
the three consecutive slice identities must be used to identify the actual
spin multiplicities and assemble the complete source equivalence. Sixth
degree, conjugate/complementary transport and general restricted-color
positive coupling remain subsequent obligations toward original endpoint 2.

The full positive-Q fifth/seventh source equivalences are subsequently
proved in the [assembly result](colored-fifth-assembly-results.md).

See [verification](colored-fifth-slices-verification.md).
