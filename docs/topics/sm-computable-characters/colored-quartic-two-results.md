# Complete quartic doublet decomposition

The two remaining components are constructed, their joint independence is
proved, and the three-branch quartic equivalence is complete. This closes
the generic doublet source identity from the
[quartic plan](colored-quartic-plan.md). Retained color/weak resolution for
Q has since been proved in the [next continuation](colored-quartic-resolution-results.md).
The original full mixed q/l support classification remains open.

Resume base: `checkpoint 01`, working branch `proof/sm-computable-characters`,
integration target `master`; no merge or push authorized.
See [verification](colored-quartic-two-verification.md).

## The proved statement

For any finite-dimensional complex representation r of an arbitrary group
G, and a homomorphism `j : G -> SU2` giving the doublet W, the actual
representation equivalence

```text
Lambda^4(A tensor W)
  = (Lambda^4 A tensor Sym^4 W)
      + (K211(A) tensor Sym^2 W) + K22(A)
```

is now proved, with the complete G action retained.
K211 and K22 are the kernels of the previously constructed actual exterior
multiplication maps, not supplied Young-module or branching premises.
There is no irreducibility, character, Weyl, or new literature assumption.

The main declaration is
`Math.ExteriorFourthDoubletCauchyRepresentation.equivalence` in
[the representation module](../../../Math/RepresentationTheory/ExteriorFourthDoubletCauchy.lean).
It has an actual linear inverse and intertwines the full action; the
doublet may be correlated with the A action through the same group G.
`complementEquivalence` also identifies the actual kernel of the earlier
top-column retraction with the remaining two components.
The linear projected insertions/extractions are explicit. The retained
representation identification cancels the actual finite top column from
the two proved equivariant splits, using the already proved
`FiniteSummandCancellation` bridge. It supplies no branching premise.

## Construction and independence

[AlternatingFour](../../../Math/LinearAlgebra/AlternatingFour.lean) groups
four-variable alternation into four three-variable alternators. Its
alternation property is proved for arbitrary multilinear maps.
[ExteriorFourthShuffle](../../../Math/LinearAlgebra/ExteriorFourthShuffle.lean)
constructs actual shuffle maps delta13 and delta22, with four-term and
three-pair formulas respectively.

[ExteriorFourthDoublet](../../../Math/LinearAlgebra/ExteriorFourthDoublet.lean)
constructs insertion J13 and contraction G13 on
`(A tensor Lambda^3 A) tensor Sym^2 W`, from the doublet determinant tensor
and alternating form. The complete universal identity is

```text
G13 J13 = 128 id - 32 ((delta13 m13) tensor id).
```

Restriction to K211 kills the second term. Projection to the actual
kernel and division by 128 give a proved left inverse of `insert211`.
Its injectivity requires no finite-dimensionality of A.

[ExteriorFourthDoublet22](../../../Math/LinearAlgebra/ExteriorFourthDoublet22.lean)
constructs J22 and G22 on `Sym^2(Lambda^2 A)` using two determinant
tensors/forms. It proves

```text
G22 J22 = 288 id - 96 delta22 m22.
```

Restriction to K22 and normalization give a proved left inverse of
`insertK22`, again without a dimension assumption on A.
The displayed constants are universal normalizations of the chosen maps,
not ranks, multiplicities, or measurements at a particular content.

[Cross contractions](../../../Math/LinearAlgebra/ExteriorFourthDoubletCross.lean)
prove that G13 J22 and G22 J13 vanish, and that both contractions vanish
on the top column. Applying the two normalized contractions to a relation
among the three summands first recovers the middle and last coordinates;
the already proved column injection then recovers the first coordinate.

[The complete linear equivalence](../../../Math/LinearAlgebra/ExteriorFourthDoubletCauchy.lean)
uses that actual injectivity with the previously proved symbolic dimension
identity to obtain surjectivity. It does not substitute equal dimensions
for constructing independent maps. The same file projects the new
insertions into the kernel of the previous column retraction and gives
explicit inverse contractions there.

[Naturality](../../../Math/LinearAlgebra/ExteriorFourthDoubletNaturality.lean)
is proved for arbitrary linear transformations of A and doublet
transformations preserving the determinant tensor. The representation
wrapper discharges the latter condition using the proved determinant-one
property of the actual SU2 doublet. It is not left as an extra theorem
premise in either final equivalence.

## Trust and scope

The algebraic identities are checked on arbitrary color vectors. Only the
fixed two-dimensional doublet coordinates and four-slot permutations are
used to normalize the universal operators. No color basis, list of SM
contents, representation rank, exact multiplicity, or Laurent coefficient
is evaluated. No retired certificate, dependency/pin change, increased
Lean limit, custom axiom, or external branching rule is used.

At this checkpoint, specializing A to color tensor weak left K211(A) and
K22(A) unresolved; the [later resolution](colored-quartic-resolution-results.md)
now discharges that obligation. This
generic equivalence does not declare them irreducible under that action
or decide all their mixed color couplings. Q degrees five/six and the
complete existing q/l support endpoint remain open.
