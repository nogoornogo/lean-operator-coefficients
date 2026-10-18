# Actual spin-weight slices with retained commuting actions

Continuation from `checkpoint 01`, branch `proof/sm-computable-characters`,
integration target `master`; no merge or push authorized. This implements
the weight-slice foundation of step 3 in the
[completion plan](colored-support-completion-plan.md). It is not yet the
Q degree-five/six application or the full q/l support classifier.

## Proved source comparison

For a jointly continuous finite-dimensional representation rho of
SU2 x K, with a proved torus bound N, and k in `Fin (N+1)`,
`SU2IsotypicSlices.equivalence` proves an actual K-equivariant equivalence

```text
Weight_k(rho) = Multiplicity_k(rho) + Weight_(k+2)(rho).
```

Weight means simultaneous eigenvectors for the **entire circle**, with
eigenvalue z^k. Multiplicity is the existing actual isotypic multiplicity
range representation, retaining every commuting K action. The complete
SU2 decomposition is constructed using the already proved bounded
isotypic models, not supplied as a new branching premise. Neither a
character difference nor equality of dimensions substitutes for this
equivalence.

## Algebraic interfaces

- `TorusWeightSlice` defines actual circle-weight subrepresentations with
  their retained action and transports them through full group
  equivalences. It requires no norm, inner product or character.
- `TorusWeightTensor` proves that a distinct basis weight in a tensor
  factor leaves the **entire** independent representation as the weight
  space. Symbolic tensor coordinates give explicit inverse maps; absent
  weights vanish. No basis or content list is expanded.
- `SU2WeightSlice.index_iff` proves the uniform interval/parity condition
  `-m <= n <= m` and `(n+m) mod 2 = 0`. Matching slices are equivariantly
  the whole retained representation; nonmatching slices vanish.
- `TorusWeightProducts` proves that complete product decompositions
  commute with actual weight spaces, including dependent carriers.
- `SU2StringSliceSum` filters a complete sum by the proved interval/parity
  condition, with an actual equivariant inverse. `SU2ConsecutiveSlices`
  splits its selected index set into the k multiplicity and the k+2 set.
- `SU2IsotypicSlices.sourceEquivalence` discharges the complete-sum input
  using existing isotypic models; its final equivalence uses only joint
  continuity and the proved source bound.

The algebraic slice lemmas work with arbitrary retained groups and module
carriers. The final continuous isotypic consumer uses the existing normed,
finite-dimensional model and a topological space on K. No compactness of
K, SU3 irreducibility, Weyl input or new literature premise is added.

## Proof size and verification

The first dependent-sum construction hit the default kernel checking limit.
Replacing equality transport of an entire representation equivalence by
`castWeight`, an explicit identity on vectors with equal weight labels,
and factoring the forward/backward maps into separate declarations fixed
the problem. A failed 94.9-second check became a successful 5.8-second
focused check at approximately 4.8 million KiB process-group RSS. These
are diagnostic timings, not mathematical inputs. No Lean limit changed.

See [verification](spin-slice-verification.md) for focused/strict/full
checks. The eight modules add 53 persistent strict transitive checks and
keep the structural numerical-import exclusions unchanged.

## Next actual-source obligation

For the exterior doublet source, identify its actual weight slice with
`Lambda^p A tensor Lambda^q A`, where p+q=n and p-q is the selected
weight. Existing occupation exhaustion and binary exterior equivalences
provide the underlying maps. `OccupationExteriorDecomposition.equivalence` now supplies the complete
actual occupation direct-sum comparison, with explicit projection and sum
inverses; different occupations have zero cross projection. The remaining
weight-space identification must still be proved. Only then may consecutive-slice
cancellation be used to resolve the remaining Q spin multiplicities.
This comparison is subsequently proved in the
[exterior-source continuation](exterior-weight-slice-results.md). General
compatible positive restricted-color coupling remains open.
