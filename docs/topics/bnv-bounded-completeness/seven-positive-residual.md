# Positive Dimension-Seven Residual Coordinates

## Verified Statement

For each of the four positive-baryon patterns, `BnvSevenResidualCoordinates.familyEquiv`
is a two-sided complex-linear equivalence from the independent orbit-supported
physical coefficient space to a submodule of an explicit residual-Hom product.
The local index sizes for `udd anti-L H*`, `qqd anti-L H*`, `qdd anti-E H*` and
`ddd anti-L H` are respectively 2, 2, 1 and 2.

The residual input is the balanced tensor of the four typed fermion
multiplicity modules and the scalar multiplicity module. Each coordinate is
an intertwiner from that tensor to the trivial complex representation.
`mem_residualSpace_iff` states exactly the remaining constraint: the synthesized
ordered coefficient obeys the actual typed identical-field exchange relation.
There is no unresolved gauge-invariance or local-spanning premise in this
membership criterion.

`nonzero_iff` and `forbidden_iff` give the existential allowance and universal
prohibition criteria for each of these four physical families.

## Proof Interfaces

- `BnvSevenFieldTensor.orderedEquiv` retains the actual exchange condition while
  replacing four multilinear slots and one linear scalar slot by a tensor.
- `regroup` separates the local gauge/Weyl tensor from the residual tensor.
  `regroupLocal` additionally separates the charged gauge and Weyl actions.
- `BnvSevenLocalTransport.localEquiv` transports each actual positive local
  tensor to a reduced core through a surjective group projection.
- `pairing_probe` and `reconstruction` prove independence and exhaustive local
  reconstruction. `flavorEquiv` extracts arbitrary residual-Hom coordinates.
- The inverse coordinate map synthesizes the actual typed coefficient. Its
  exchange relation defines the residual submodule and is transported in both
  directions, not supplied as an external classification assumption.

## Assumptions And Boundary

The residual group and its algebraic actions are arbitrary. Fermion and scalar
multiplicity modules need not be finite-dimensional. Independent signed
species are not identified with dual or conjugate flavor modules. The scalar's
residual action is retained, not assumed trivial.

Only the four positive-baryon dimension-seven families are classified here.
The four negative-baryon families, the scalar-free signed endpoint, the full
seven-dimensional gate, and the dimension-eleven stop gate remain open.
This checkpoint does not assert a new literature-wide comparison.

## Verification

Focused local and residual-coordinate builds pass. Persistent transitive axiom
audits pass (151 checks); full `lake build` passes (6,472 jobs). Layout passes
(1,145 modules), links pass (442 Markdown files, 2,950 links), and
`git diff --check` passes.
