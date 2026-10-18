# Actual 40/50 Kernel Constructions

The first construction checkpoint of [the actual-exotic plan](actual-exotic-plan.md)
is proved. The full requested branching/arbitrary-mass endpoint remains open.
This is new actual-representation evidence, unlike the earlier formal profiles.

## Actual SU(5) modules

[ExoticWedgeKernel](../../../GUT/SU5/Representations/ExoticWedgeKernel.lean)
constructs the equivariant surjective map

```
Five tensor wedge² Five -> wedge³ Five
x tensor (y wedge z) |-> x wedge y wedge z.
```

Its actual invariant kernel has dimension 40. Taking its algebraic dual
matches the convention chosen in the formal-character computation.
`wedge_surjective`, `kernel_finrank`, `representation_finrank` and
`representation_character` are proved. The latter is the actual trace
identity obtained from the exact sequence and duality, not assumed character
input. The proof uses the exterior universal property and explicit pure wedges.

[ExoticSymmetricKernel](../../../GUT/SU5/Representations/ExoticSymmetricKernel.lean)
constructs the equivariant surjective map

```
Sym²(wedge² Five) -> wedge⁴ Five
(a wedge b) symmetric-product (c wedge d) |-> a wedge b wedge c wedge d.
```

Degree-two exterior factors commute, so the map descends to the independently
constructed symmetric-power quotient. The actual invariant kernel has dimension
50: source dimension 55 and target dimension 5. Surjectivity is proved by
lifting every pure four-wedge. `product_covariant`, `wedgeMap`,
`wedge_surjective`, `kernel_finrank` and `kernel_character` are proved.

Both kernels are genuine algebraic representations of the actual SU(5) group.
No supplied list of weights, characteristic matrix, custom axiom or external
oracle defines their action or proves their dimensions. Irreducibility,
continuous/unitary realizations and full SM branching equivalences are not
asserted as new proved results at this checkpoint.

## Connection gate after the construction

The actual trace identities now justify the tensor/exterior/symmetric
character differences at the representation level. They do not by themselves
identify the previous Python SM blocks with actual equivariant subspaces.
The next missing theorem is selected-species extraction, including proof that
all opposite-species contributions have been accounted for.

A route through explicit SM decomposition must split the remaining color/weak
tensor factors (including sextet/octet and higher weak factors), derive the
needed Hom/pairing exclusions, and connect them to these kernels. Alternatively,
a faithful actual-character extraction route needs certified evaluator and
multiplicity identities for the constructed modules. No such final connection
is silently obtained from dimension 40/50 or the finite-profile certificate.

The inspected fundamental/ten branching assets do not already supply this
extended decomposition, and `SpeciesSectorPresentation` still requires its
coordinates and NoPairings proofs. Thus arbitrary invariant mass on the
extended actual carrier has not yet been classified. The finite-character
script remains independent supplemental evidence, not a premise.

## Status and bounded stop

Completed: actual invariant kernels, equivariance, surjectivity, dimensions,
and exact trace differences, with strict audits and full build.
Open: selected/full SM branching, continuity if the chosen character route
needs it, sector/pairing exclusions, and all-mass physical qque connection.

This reaches the recorded construction-to-branching prerequisite gate.
Do not mark the entire requested physical endpoint complete. A subsequent
milestone must freeze either the explicit selected-species decomposition or
the faithful-character extraction route before adding new branching helpers;
no general Young/continuous representation classification is started here.
No nonzero physical qque or exact SM mass spectrum follows yet.
