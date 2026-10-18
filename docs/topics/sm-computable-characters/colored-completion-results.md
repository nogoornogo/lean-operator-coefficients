# Colored exterior and positive SU3 continuation

Continuation from `checkpoint 01` on `proof/sm-computable-characters`, targeting
`master` without merge/push authorization. The user requested consecutive
attempts at complete colored exterior branching and compatible positive
SU3 coupling. This pass proves the results below in that order; **neither
general endpoint is marked complete**. The original full q/l classification
remains open. See the [plan](colored-completion-plan.md),
[remaining semantic bridges](colored-completion-boundary.md) and
[verification](colored-completion-verification.md).

## Exterior branching and actual Q consumer

`SymmetricSquareCauchy.equivalence` proves

```text
Sym^2(A tensor B)
  = (Sym^2 A tensor Sym^2 B) direct-sum (Lambda^2 A tensor Lambda^2 B).
```

Its quotient maps, sections, four scalar composites and reconstruction
identity are constructed on arbitrary vectors. Both inverses are proved;
no basis dimension, rank, multiplicity or branching hypothesis is supplied.
`SymmetricSquareCauchyRepresentation` retains arbitrary group actions.
`ExteriorSquareTriple` combines this split with the previously proved
exterior-square Cauchy equivalence and tensor/product distribution.

`SU3DoubleSpinSquare.positive` gives the actual Q-core square branches:

| Color | Weak highest weight | Spin highest weight |
| --- | --- | --- |
| dual defining | 2 | 2 |
| dual defining | 0 | 0 |
| symmetric color square | 0 | 2 |
| symmetric color square | 2 | 0 |

`negative` gives dual color with the corresponding conjugate color
branches. `SU3DoubleSpinExterior.negativeInputEquiv` identifies the actual
dual gauge input with dual color tensor the original weak doublet, using
its proved alternating duality. It does not identify the independent spin
factors. Determinants are one; capacity is twelve. Complementary exterior
duality supplies complete degree-ten branches as duals of the square.
No middle degree is inferred from this square/complement result.

`SMQCoreBranching` proves the actual signed-core identifications for Q
(species 0, left spin) and conjugate Q (species 5, right spin), and transports
the degree-two/ten decompositions while retaining the full semisimple group.

`SMQPairHiggsSupport.original_ql_iff` proves actual three-generation
`Q^2 conjugate-Q^2` permission iff `h=d`, for every Higgs bidegree and every
existing cyclic scalar q/l assignment. Surjective projections onto the
opposite-color, weak/spin-scalar square branches give an actual nonzero
color evaluation coefficient. The proved generation projection, statistical
source transport and Higgs/charge consumers complete both directions.
Thus a separate color singlet in either Q block is not required. No unknown
`Allowed`, Weyl input or numerical rank remains in this family.

## Positive color coupling and compatible joint labels

`InvariantCoefficientProduct` proves that scalar permission is equivalent
to an actual coefficient/vector pair evaluating to one. Such witnesses
transport through equivariant equivalences and tensor without any
irreducibility premise. Its hypotheses require only additive monoids and
complex modules; no extra group structure on a tensor carrier is assumed.

`SU3TensorPositive.positive` constructs normalized coefficients for
unrestricted defining/dual color tensor powers whenever `a mod 3=b mod 3`.
The construction uses evaluation pairs and defining/dual determinant
triples, tensoring and regrouping them for arbitrary degrees. Conversely,
`SU3TensorTriality.necessary` applies the actual scalar center at a primitive
cube root. The resulting closed theorem is

```text
Allowed(Invariants(V^(tensor a) tensor V*^(tensor b)))
  iff a mod 3 = b mod 3.
```

`SU3ColorTensorWord.equivalence` normalizes every ordered binary tensor word
of defining/dual color into those powers. `allowed_iff` and `forbidden_iff`
therefore decide all such words, including arbitrary parenthesization and
ordering. This is not an assertion about their symmetric/exterior quotients.

For actual restricted branches, `SU3ColorPositive.symmetric_unit` supplies
a normalized coefficient for `Sym^m(V) tensor Sym^m(V*)`, uniformly in m,
using the existing proved symmetric dual pairing. `TraceFreePairing.unit`
constructs a normalized coefficient on two trace-free endomorphism factors:
trace of composition is invariant, and opposite off-diagonal rank-one
endomorphisms pair to one. The proof is uniform in the representation and
basis and assumes neither adjoint irreducibility nor a dimension table.
Both defining-color and dual-color trace-free branches are covered.

`ExternalCoefficientSupport.allowed_iff` proves exact factorization for
independent group actions by slicing a nonzero coefficient and constructing
its tensor product converse. The factors are the *whole regrouped* color
and weak/spin sources; no specieswise singlet test is introduced.
`SU3CompatibleCoupling` then proves simultaneous iff criteria:

- unrestricted ordered color words: triality, plus equality of both joint
  SU2 labels;
- a matched symmetric-color/dual-color pair: equality of both SU2 labels;
- two defining-color trace-free branches, or two dual-color trace-free
  branches: equality of both SU2 labels.

These keep nonsinglet intermediate weak/spin representations and include
both witnesses and exclusions in their stated ranges. They do not decide
arbitrary mixed restricted color products. In particular triality has not
been asserted sufficient after passing to a chosen Schur summand.

## Assumptions and remaining work

The results use no new external mathematical input, custom axiom, dependency
change, proof-limit increase or numerical content certificate. Fixed scalar
normalizations in the square maps, determinant triples, and scalar-center
roots are universal algebraic constructions, not multiplicity evaluation.

Complete Q middle-degree branching and the general positive coupling rule
for all reachable restricted color summands remain unproved. The inspected
library/literature routes and the exact additional semantic statements are
recorded in the [boundary](colored-completion-boundary.md); neither was
inserted as a theorem parameter. The new bounded positive families and
actual Q consumer do not complete original endpoint 2.
