# Internal Linear Actions And Mixed Jets: Implementation Contract

Status: A/B proof and build gates completed. Work remains on
`proof/derivative-ibp`, targeting `master` only after separate merge direction.
This contract implements A/B of the [assessment](extension-assessment.md).
The completed scalar contract and its verification remain separate evidence.
Keep Lean, Mathlib, TauCeti, Physlib and optional documentation pins unchanged.

## Frozen Source And Statements

Work over ℂ with ordinary, commuting, off-shell derivative symbols. A jet
index is a component label together with a finite-support natural multi-index.
There is no maximum jet order and no factorial or momentum normalization.
The component module is a free module in a specified basis; a linear map on
that module may mix components arbitrarily and fixes derivative indices.
This covers finite-dimensional field representations after choosing a basis.
Finite component and direction sets are required only for finite-grade claims.

A must construct functorial jet maps and arbitrary internal representation
actions, prove covariance with actual total derivatives and preservation of
grades, and connect the free symmetric presentation to the existing scalar
polynomial presentation in both directions. Include a non-permutation shear
and recovery of the degree-zero field action. Local/residual actions are
parameters; prove their commutation and stability rather than assuming a
quotient theorem's hypotheses as the result.

B must construct the actual mixed algebra on one exterior algebra of all odd
jets and the symmetric algebra of all even jets (a proved polynomial
presentation is permitted). Differentiation is even, so its Leibniz rule has
no statistics sign. Prove generator formulas and pairwise commutation.

Construct grades `(nF,nB,d)`, actual graded derivative maps and finite fixed
grades for finite component/direction sets. Prove the semantic bridge to the
existing `MixedPowerDescent.Domain = Λⁿ J_F ⊗ Symᵐ J_B` source, including inverse
coefficient transport and the derivative-free boundary. A named wrapper or a
surjectivity claim without the inverse/source identification is insufficient.
IBP may move derivatives between factors, so do not independently quotient
derivative-distribution sectors.

For each target grade `(nF,nB,d+1)`, currents are the finite-support direction
sum of the preceding grade; relations are exactly the range of the actual
divergence. Prove range stability, annihilation iff all derivative evaluations
vanish, inverse coefficient descent and the local/residual-Hom correspondence
for commuting internal linear actions. These are linear source quotients,
not ideals or field-space/dual identifications.

## Concrete Acceptance Consumer

Use one even component `φ`, one odd component `ψ`, one direction, and grade
`(nF,nB,d)=(2,1,2)`. Prove full source span by
`A=φ₁ψ₀ψ₁`, `B=φ₀ψ₀ψ₂`, full preceding-current span by `φ₀ψ₀ψ₁`, and
`D(φ₀ψ₀ψ₁)=A+B` with the `ψ₁²=0` cancellation in the actual exterior algebra.
Prove the entire relation span, an explicit quotient equivalence with ℂ and
a surviving class. Relations must be derived from the total derivative.

## Milestones, Verification And Stops

1. A: jet linear functor, scalar presentation bridge, covariance, finite-grade
   transport and non-permutation consumer.
2. B: mixed algebra/derivative, actual-source bridge, joint grades and finite
   fixed grades, then stable actual divergence and inverse coefficient descent.
3. Complete the mixed consumer, register all sources/audits in `Math.lean`,
   reconcile result/source/assumption records and the bibliography, and commit
   coherent verified milestones while continuing through the endpoint.
4. Run focused builds, persistent strict transitive axiom audits, full
   `LEAN_NUM_THREADS=4 lake build`, layout, local links, topic index, portable
   metadata and diff checks. Standard axioms only; no policy exceptions.

Stop successfully after all these gates. Stop with a precise verified partial
result if a necessary bridge requires changed dependencies, extra mathematical
or physical premises, audit exceptions, increased recursion/kernel limits or
an independent foundation outside A/B. For a named costly check retain the
operational ceiling of 16 GiB process RSS / nine minutes. Diagnose a failed
route before selecting a different construction; do not retry it under a new
name. A coherent intermediate commit alone is not a stopping condition.

Direction mixing, actual Lorentz specialization, EOM, Bianchi relations,
gauge-covariant derivatives, analytic integration, amplitude equivalence,
momentum-symbol comparison and general EFT enumeration are excluded. They
require another implementation contract after A/B evidence is available.

## Gate Outcome

A/B gates pass. The implementation uses the actual exterior algebra tensored
with a polynomial presentation of the even symmetric algebra. The new
symmetric-power/polynomial equivalence and injective mixed embedding supply
the actual-source connection, its grade restrictions and inverse coefficient
transport. The zero-derivative boundary recovers the existing mixed source
equivariantly. Grades are defined as spans of actual words, with multiplication,
derivative shift and finite-dimensionality proved; a new global direct-sum
decomposition is not asserted.

The mixed consumer proves the complete source/current spans, the Pauli
cancellation, the entire divergence range, quotient equivalence with ℂ,
dimension one and a surviving class. The persistent audit passes 223 strict
transitive checks, full build passes 7594 jobs and layout passes 2100 modules.
The [result dossier](../../proof/current/core/Math/MIXED_JET_IBP.md) and
[verification](verification.md) record the final gates and scope.
This is the successful A/B stop; C–E implementation and master integration
are not performed.
