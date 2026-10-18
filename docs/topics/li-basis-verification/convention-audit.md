# Qque Convention And Certificate Audit

## Literature Object

Li--Ren--Xiao--Yu--Zheng distinguish a flavor-blind `y`/`m` basis from a
`p`-basis obtained after imposing the permutation statistics of repeated
fields.  In section 3.3, equation (67) expresses this as the bosonic or
fermionic sign under the relevant symmetric-group action.  Their model output
uses charge-conjugate field notation such as `u_C` and `e_C`; the dimension-six
SMEFT type table contains the candidate type rendered in the HTML output as
`ec^dagger Q^2 uc^dagger`.

The paper does not use this repository's internal identifier `qque`, and the
displayed type name alone is not a proof that the two conventions coincide.
The precise ABC4EFT output, field order, chirality convention and normalization
must therefore be recorded before importing any coordinate array.

## Repository Object

The intrinsic coefficient endpoint is
[`QqueCoefficientCompleteness.equiv`](../../../Physics/StandardModel/Operators/QqueCoefficientCompleteness.lean):

```text
IntertwiningMap (SymmetricPower 2 A) (B tensor D)
  ~=
degree-(2,1,1) invariant exterior coefficient sector.
```

Its actual fields are identified with

```text
Q : (Color tensor Weak) tensor A, left Weyl,
U : Color tensor B.dual,          right Weyl,
E : C tensor D.dual,              right Weyl.
```

Only `B` and `D` are required finite-dimensional for this Hom presentation;
`A` and the abstract residual group are unrestricted.  The independent sector
is derivative-free and already includes the full exterior/Fermi statistics.

[`QquePhysicalExteriorCompleteness.permutation_statistics_iff`](../../../Physics/StandardModel/Operators/QquePhysicalExteriorCompleteness.lean)
proves that the repeated-`Q` exterior constraint is equivalent to symmetry in
the two residual `Q` inputs.  Thus the coefficient-side counterpart of the
two-field p-basis permutation condition is already proved.  This does not by
itself identify a finite list of flavor-specified operators.

## Required Dictionary

Before claiming a literature check, the following equalities must be explicit:

1. `Q` is matched with the same left-handed SM quark-doublet convention.
2. Li's charge-conjugate singlets, including each dagger, are matched with the
   repository's right-Weyl carriers and the `B.dual`/`D.dual` residual action.
3. The external-slot order is related to the repository order `Q,Q,U,E`, with
   all fermionic permutation signs accounted for.
4. The color, weak and Weyl contractions have the same normalization, or an
   explicit nonzero change-of-basis scalar is proved.
5. Operator flavor tensors and coefficient tensors are related by a stated
   finite-dimensional duality; they are not silently identified.

## Certificate Path

Once the dictionary is fixed, the existing
[`FiniteLocalBasisConversion`](../../../Math/RepresentationTheory/FiniteLocalBasisConversion.lean)
API supplies exact forward and inverse conversion between two independently
normalized and exhaustive finite local contraction dictionaries, while retaining
arbitrary residual coefficients.  The qque pilot additionally needs a finite
flavor basis for the Hom space and a proved map from each literature operator to
that basis.  An external rank statement may be used to discover an inverse, but
the inverse identities must be checked by Lean.

No new generic coordinate structure is currently needed: adding one would
duplicate `LinearEquiv`, `FiniteInvariantFactor` and
`FiniteLocalBasisConversion`.  The next implementation step is the convention
adapter, not another abstract basis package.

## Checked Dictionary And Boundary

The [proof dossier](../../proof/current/applications/Physics/LI_QQUE_BASIS.md) records the implemented
semantic adapter and coordinate certificate. `paperOrdered_apply` is the
literal normalized (D.38) contraction in `Q,Q,E,U` order; `fermionic_reorder`
proves the Fermi/bracket sign cancellation. `candidate_probe` retains the factor
2 from raw alternatization. Constructed gauge bidual maps supply the algebraic
dagger dictionary; arbitrary physical conjugate fields still need explicit
identifications with it.

`equiv_symm_tprod`, `residual_entry` and `flavor_paperOrdered_apply` connect
coefficient duality, finite entries and the printed contraction. The matrix
rows follow U,E order, so the paper's final E,U flavor indices are reversed in
this coordinate convention. Symmetric-power basis columns are unordered Q pairs.
For arbitrary H, the coordinate domain is constrained by intertwining equations;
individual matrix units are not automatically invariant. The unrestricted
finite basis theorem applies to trivial residual action.

The paper route uses (D.38), recovered and visually checked in the PDF appendix.
Its brackets are interpreted using explicitly normalized alternating pairings.
No general on-shell-amplitude correspondence or physical normalization follows
from this dictionary. No ABC4EFT runtime array was executed or certified.
The original semantic and inverse gates are handled for this explicit local
interpretation; broader literature/package claims remain outside the endpoint.

## Sources

- [Li et al., section 3.3 (p-basis)](https://arxiv.org/html/2201.04639v2#S3.SS3)
- [Li et al., section 4.3 (basis conversion)](https://arxiv.org/html/2201.04639v2#S4.SS3)
- [ABC4EFT project page](https://abc4eft.hepforge.org/)
