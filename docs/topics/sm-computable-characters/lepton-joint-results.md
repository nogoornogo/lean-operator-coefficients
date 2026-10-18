# Complete joint lepton branching without numerical certificates

Continuation from `checkpoint 01` under the user's direction to carry out the
[limited foundation plan](limited-foundation-plan.md). No dependency pin,
physical convention or external-mathematics premise changed. The new
results do not use the optional Weyl input. They do not complete the
original mixed q/l classification.

## Single-generation core

[`SU2PairExterior`](../../../Math/RepresentationTheory/SU2PairExterior.lean)
constructs the complete exterior decomposition of two independently acting
doublets. Labels are SU2 highest weights, twice the physical spins.

| Exterior degree | Joint labels (weak, spin) |
| --- | --- |
| 0 | (0,0) |
| 1 | (1,1) |
| 2 | (2,0) and (0,2) |
| 3 | (1,1) |
| 4 | (0,0) |
| Above 4 | zero |

The two Cauchy injections at degree two are proved independent and exhaustive.
`DistinctIrreducibleAssembly.injective_of_inequivalent` handles the
equal-dimensional but inequivalent joint factors. The former dimension-distinct
helper remains a special case. Exhaustion uses structural symmetric/exterior
dimension identities; no numerical rank or multiplicity certificate is
evaluated. Upper degrees use determinant-one complementary duality.

## Complete positive tensor coupling

[`FiniteExternalProducts`](../../../Math/RepresentationTheory/FiniteExternalProducts.lean)
constructs equivariant finite-product distribution, termwise transport and
dependent-family flattening using mathlib tensor/product equivalences.
[`SU2PairCoupling`](../../../Math/RepresentationTheory/SU2PairCoupling.lean)
combines the proved SU2 Clebsch--Gordan decompositions. Pairs `(a,b)` and
`(c,d)` contain target `(u,v)` exactly when

```text
Triangle(a,c,u) and Triangle(b,d,v),
Triangle(x,y,z) := z<=x+y and x<=y+z and y<=x+z and (x+y+z)%2=0.
```

[`SU2PairDecomposition`](../../../Math/RepresentationTheory/SU2PairDecomposition.lean)
iterates these complete decompositions, retaining repeated copies and both
intermediate labels. Pair and triple exterior products have a necessary-and-
sufficient positive path rule made of only core branches and triangle/parity
conditions. No unknown Hom or signed coefficient remains in those rules.

## Closed three-generation joint classification

[`SU2PairGenerationSupport`](../../../Math/RepresentationTheory/SU2PairGenerationSupport.lean)
uses complete generation exhaustion and canonical content-tree words. Each
generation occupation is at most four and their sum is the total degree;
no search over generation words is evaluated.

[`SU2PairGenerationBounds`](../../../Math/RepresentationTheory/SU2PairGenerationBounds.lean)
proves the paths exist **exactly** when

```text
n <= 12,
a <= n, b <= n, a <= 12-n, b <= 12-n,
a+b <= 6,
a%2 = n%2 and b%2 = n%2.
```

Necessity adds constituent bounds and transports parity separately.
Sufficiency constructs occupation and Clebsch--Gordan paths at the lower-half
degrees; complementary occupations cover the upper half. No exact positive
multiplicity is asserted or evaluated. The final condition has no Hom or path
search. Arithmetic proofs use small separate lemmas, not one large solver call.

[`SMLeptonCoreBranching.source_target_iff`](../../../Physics/StandardModel/Operators/SMLeptonCoreBranching.lean)
connects the criterion to the actual statistical constant-L source. The
retained semisimple group includes color, weak and **independent** left/right
spins; a proved surjective projection removes only factors trivial on both
source and target. Field identifications are proved. Hypercharge is one only
in this restriction; existing charge consumers must reattach hypercharge and
q/l conditions. A nonsinglet left-spin constituent is not an allowed scalar
operator by itself: its spin must cancel in the complete mixed source.

## Color foundation and remaining scope

[`SU3DefiningExterior`](../../../Math/RepresentationTheory/SU3DefiningExterior.lean)
proves actual defining SU3 exterior identifications: degree one is defining,
degree two contragredient, zero/top are scalar lines and overflow is zero.
Scalar support is exactly degrees zero and three. This concerns the **pure
SU3 action**; no hypercharge determinant twist in an SM field is discarded.

[`TraceEndomorphismSplit`](../../../Math/RepresentationTheory/TraceEndomorphismSplit.lean)
constructs the scalar/trace-free conjugation decomposition of endomorphisms
for a finite-dimensional representation of nonzero dimension. Its dimension
assumption is explicit. [`SU3ColorPair.equivalence`](../../../Math/RepresentationTheory/SU3ColorPair.lean)
discharges it on the defining color representation and transports the split
through mathlib's actual `Representation.Equiv.dualTensorHom` to
`3 tensor dual(3)`. It constructs a nonzero scalar coefficient and a linear
equivalence of the **entire** scalar coefficient space with the scalar field.
Schur's lemma excludes fixed vectors in the trace-free summand; its
irreducibility and later tensor-product support are not assumed or proved.

The colored one-generation cores `(3 tensor 2)` and `(3 tensor 2 tensor 2)`,
their conjugates, the independent second chirality, and compatible cross-species
color couplings still need their target-occurrence proofs. The closed L rule
supplies every nonsinglet weak/left-spin target, but it does not decide those
colored occurrences or the original full q/l support classification. No
wanted positivity is imported as a premise. See
[the exact remaining colored obligations](colored-core-boundary.md) and
[verification](lepton-joint-verification.md).
