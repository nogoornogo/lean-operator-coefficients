# Signed mixed-lepton all-Higgs support

Continuation from `checkpoint 01` on `proof/sm-computable-characters`. This proves
a complete actual mixed subfamily of endpoint 2, not the full ten-species
classification. No merge, push, numerical certificate, new external premise
or dependency change.

## Exact criterion

Let a be the number of L fields (signed species 3), b the number of conjugate
L fields (species 8), and C(n) = min(n,12-n). Retain three generations,
independent left/right spins, h Higgs fields, d dual Higgs fields and the
existing scalar cyclic q/l action of any nonzero order. Then
`SMMixedLeptonSupport.original_ql_iff` proves:

```text
Allowed(original coefficient space)
  iff a*l-b*l = 0,
      a <= 12 and b <= 12,
      a and b are even,
      h-d = a-b,
      -(C(a)+C(b)) <= a-b <= C(a)+C(b).
```

The differences and signed inequalities are integral; residual charges are
in `ZMod k`. All h,d are allowed as parameters. The right side has no
unknown Hom, `Allowed`, representation isomorphism, multiplicity, rank,
character coefficient or Weyl input. q is arbitrary and drops out because
this family has no quarks. Permission concerns an actual nonzero invariant
coefficient; it does not assert a generated interaction or rate.

[`SMMixedLeptonWord.original_ql_iff`](../../../Physics/StandardModel/Operators/SMMixedLeptonWord.lean)
extends this rule to every ordering with the same occupation counts.
`original_eq` proves equality of the original supported coefficient
subspaces for equal-count words, rather than a counting-only assertion.
`balanced_ql_iff` specializes a=b: permission is exactly a<=12, a even and
h=d, at every cyclic q/l assignment.

## Why the rule is sufficient as well as necessary

[`SMLeptonMaximalLocal`](../../../Physics/StandardModel/Operators/SMLeptonMaximalLocal.lean)
uses the complete joint L rule to construct a nonzero coefficient in the
maximal spin-zero weak constituent C(a), including complementary exterior
degrees. The proved conjugation transport constructs the conjugate block
at C(b); its hypercharge phase has the opposite sign. These local
constituents are not separately asserted to satisfy an isolated all-Higgs
admissibility condition.

[`InvariantCoefficientGluing`](../../../Math/RepresentationTheory/InvariantCoefficientGluing.lean)
curries each nonzero coefficient to the dual irreducible boson target.
Those maps are surjective. Their tensor product, followed by the dual of
an injective boson coupling, stays surjective and nonzero.
[`TwistedSU2ConstituentCoupling`](../../../Math/RepresentationTheory/TwistedSU2ConstituentCoupling.lean)
supplies that actual Clebsch--Gordan embedding, adding character charges
exactly. [`SMLocalCoefficientGluing`](../../../Physics/StandardModel/Operators/SMLocalCoefficientGluing.lean)
transports the source tensor through the actual binary statistical-source
equivalence. Its distinct-species hypothesis is essential: unrestricted
multiplication of overlapping fermion blocks is not assumed nonzero.

For the present family, |a-b| is an allowed coupling of C(a) and C(b).
The upper triangle inequality is the criterion above; the lower triangle
inequalities follow from the complementary capacity function on [0,12],
and the parity condition follows from even a,b. The resulting weak degree
|a-b| is admissible for every h,d with h-d=a-b. This constructs the allowed
direction on the original coefficient space.

Necessity uses the actual species capacity, **separate** left/right
chirality centers, hypercharge, residual charge and the sharp complementary
mixed weak bound. [`SMMixedLeptonDictionary`](../../../Physics/StandardModel/Operators/SMMixedLeptonDictionary.lean)
proves the occupation, charge and bound identities for the real signed
species; none is a new input premise.

## Scope and verification

All seven new modules use structural algebraic proofs; there is no rank or
multiplicity evaluation, enumeration of occupation cases, large basis or
new literature input. A label-transport helper specializes equalities
before the large concrete statistical carrier, keeping default Lean proof
limits unchanged.

The [plan](mixed-lepton-plan.md) is achieved for this family. The
[colored-core obligations](colored-core-boundary.md) still block full
endpoint 2: complete colored exterior branching and compatible positive
color coupling have not been proved. This mixed-lepton iff does not remove
those obligations or classify other mixed families by analogy.
See [verification](mixed-lepton-verification.md).
