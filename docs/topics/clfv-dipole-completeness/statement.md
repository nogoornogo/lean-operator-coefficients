# Frozen Dipole Interfaces

## General Extraction

For independent groups K and H, let T be a local K representation and X a
residual H representation. A local invariant functional p and v with p(v)=1
and every local invariant k = k(v) p give an equivalence

```text
Hom_(K x H)(T external X, C) = Hom_H(X, C).
```

The source is the entire independently specified intertwiner space.
Uniqueness is a theorem parameter in the general lemma, not an axiom and
not a proof that the concrete dipole contraction is unique.

## Physical Channels

Work with the algebraic covering SM gauge group already in the repository.
In the all-left conjugate convention L has integral hypercharge -3, Ec has
+6, and conjugate Higgs has -3. Their total charge vanishes. The weak dual
of the Higgs is identified using the SU(2) epsilon tensor; that identification
must be proved, not replaced by a hypercharge argument.

The B field strength is a weak singlet. The W field strength is a weak
triplet. The chiral Lorentz field strength is the dual symmetric square of
the selected Weyl space, paired with the symmetric two-spinor component.
The weak singlet contraction is alternating; the weak triplet contraction
is symmetric. Local uniqueness must include exclusion of the other
two-spinor component and any opposite-chirality contribution if such a
contribution is included in the independent sector.

At the bounded endpoint select one chiral sector and its Hermitian conjugate
by convention; a real two-form/Hermitian-Lagrangian classification is a
separate boundary. Treat B and W as distinct species: the total coefficient
space is their direct sum, not a chosen photon combination.

The two participating fermion species are distinct. Ordered coefficients
are multilinear in each of L, Ec, conjugate Higgs and field strength; the
fermionic antisymmetric extension must not impose a spurious symmetry on
the L/Ec multiplicity map. Bosons do not belong in a four-fermion exterior
power.

The expected residual description, with Higgs and field strengths residual
trivial, is one copy of Hom_H(A,B) per gauge channel, where L carries A and
Ec carries B dual. Finite dimensionality of B supplies bidual transport.
The full sector must be defined before assembly and proved to be exhausted.

## Flavor And Generation

A prescribed linear selector P acts on the classified coefficient space D.
Its interpretation requires explicit flavor identifications; no mass basis
is derived. For arbitrary X and F : X -> D:

```text
vanishing inputs = {x | P(F(x)) = 0}
exists nonvanishing input iff image F is not contained in ker P
P = 0 implies every input vanishes
surjective F implies allowed iff realized
```

The image criterion alone is a general interface, not a concrete structural
sufficiency theorem. Structural sufficient conditions must expose witnesses
or derive nonvanishing from independently checkable input data. Nonlinear
generation and a restricted input domain are permitted from the outset.

## Stop Condition

Finish after concrete local completeness, residual equivalences and the
flavor/generation interfaces are proved and audited. Do not recursively
formalize loop integration, electroweak matching, vacuum minimization or
experimental inference to complete this algebraic endpoint.
