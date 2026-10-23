# Finite-Multiplicity Cyclic Residual Selection

## Result

For generation-dependent diagonal cyclic charges, the independently defined
signed dimension-six four-fermion sector is linearly equivalent to a product
of four spaces of functions on residual-neutral independent flavor indices.
The corresponding LLHH sector is a space of functions on neutral unordered
lepton pairs. Empty index sets give zero spaces; nonempty sets give explicit
nonzero coefficients through the inverse equivalences.

## Inputs And Assumptions

Supply a positive natural cyclic order `N`, five independently chosen finite
index types with decidable equality, and charge maps into `ZMod N`. Carriers
are the complex function spaces on those indices. Different dimensions,
including zero, are admitted. The group is `Multiplicative (ZMod N)`.
The first five charges refer to physical q, u_R, d_R, l, e_R carriers;
the remaining signed species use the opposite charges and the same indices.
Higgs is a single residual-neutral doublet.

No equal-generation, genericity, anomaly or UV-generation premise is required.
This is not an algorithm for arbitrary nonabelian residual representations.

## Independent Coordinates

| Sector | Independent flavor indices | Neutrality test |
|---|---|---|
| DUQL | ordered d,u,q,l tuple | d_i + u_j + q_k + l_t = 0 |
| QQUE | unordered Q pair, ordered u,e | q_i + q_j + u_k + e_t = 0 |
| DUUE | ordered u,u,d,e tuple | u_i + u_j + d_k + e_t = 0 |
| QQQL | lepton index and symmetric/alternating/mixed triple index | q_i + q_j + q_k + l_t = 0 |
| LLHH | unordered lepton pair, including diagonal entries | l_i + l_j = 0 |

DUUE's unrestricted ordered up pair is the result of solving its local exchange
system, not an omission of Fermi statistics. QQQL uses sorted weak triples in
the symmetric branch, strictly sorted triples in the alternating branch, and
the existing repeated-pair/distinct-triple mixed coordinates. A repeated mixed
index `(i,j)` carries `2q_i+q_j`; the two distinct-triple mixed coordinates carry
the same total charge. Neutral ordered triples are not independently counted.

Each finrank is exactly the cardinality of its neutral independent index set.
The full signed sector's finrank is the sum of the four cardinalities.
It is forbidden iff every one of these sets is empty, and allowed iff at least
one is nonempty. `simultaneous_iff` adds existence of a neutral LL pair.

## Proof And Source Interfaces

[CyclicWeightCoordinates](../../../../../Math/RepresentationTheory/Weights/CyclicWeightCoordinates.lean)
proves that invariant functionals in a weight basis vanish precisely on
nonneutral indices, using the faithful character's proved injectivity.
Its inverse is zero extension. Tensor and symmetric-power weight rules are
proved without assuming invariance equivalent to neutrality.

[SymmetricTensorFunctional](../../../../../Math/RepresentationTheory/Symmetric/SymmetricTensorFunctional.lean)
descends symmetric tensor functionals through the symmetric square. This keeps
the physical carrier convention intact: no new identification with a physical
dual or bidual carrier is assumed.

[TripleFlavorWeights](../../../../../Math/RepresentationTheory/Content/TripleFlavorWeights.lean)
proves that diagonal scaling commutes with all three triple-coordinate
reconstruction dictionaries. Thus the existing alternating and mixed branches
provide the needed statistics weight blocks without a new exterior-basis
foundation. [QqqlDiagonalCoordinates](../../../../../Physics/StandardModel/Operators/BaryonOne/Qqql/QqqlDiagonalCoordinates.lean)
converts the actual reconstructed residual equations to neutral support and
proves extraction/reconstruction and cardinality formulas. Arbitrary finite
indices are reindexed through `Fintype.equivFin`; this is a proved basis
reindexing, not an equal-dimension restriction.

[FlavoredCyclicCoordinates](../../../../../Physics/StandardModel/Operators/Selection/FlavoredCyclicCoordinates.lean)
connects the other four sectors. [FlavoredCyclicSelection](../../../../../Physics/StandardModel/Operators/Selection/FlavoredCyclicSelection.lean)
composes these with the existing all-signed-species completeness equivalence;
it does not assume the four-family support as a new input. Both inverse
identities, total finrank, prohibition and allowance are explicit theorems.

## Controls And Verification

[Controls](../../../../../Physics/StandardModel/Operators/Selection/FlavoredCyclicControls.lean)
recover the scalar singleton family-charge criterion and LLHH criterion.
They also certify zero-dimensional inputs, unequal dimensions `(2,1,0,3,1)`,
the trivial-charge three-generation dimension 273, and quark parity.
A nonuniform Z2 QQQL example has four neutral ordered triples but only three
independent coefficients. These finite computations use `decide +kernel`,
not an external rank calculation or `native_decide`.

The [strict audit](../../../../../Physics/StandardModel/Operators/Selection/Audit/AuditFlavoredCyclicSelection.lean)
checks transitive axioms and excludes model-layer imports. Verification commands
and integration status are maintained in the [topic](../../../../topics/flavored-cyclic-selection/README.md).

## Boundaries And References

Allowed means a nonzero invariant coefficient exists, not that a model generates
it. No anomaly cancellation, Yukawa compatibility, quantum exactness, rate,
derivative/EOM/IBP classification or AutoEFT interface is claimed.
General six-quark flavor selection remains separate.

This result extends the [one-generation criterion](RESIDUAL_SELECTION_CRITERIA.md)
and uses the [signed four-family completeness](../../../../topics/delta-l-one-completeness/README.md).
No external literature statement is introduced as a theorem premise.
