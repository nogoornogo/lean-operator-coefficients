# Linear EOM And Weyl Contract

Status: frozen before source implementation.
Working branch: `proof/linear-eom-weyl`.
Parent/integration target: `proof/derivative-ibp`; bounded child exception.

## Mathematical Endpoint

1. A specified complex linear map from an equation module to the actual jet
   generator module gives component-mixing constant-coefficient equations.
   Construct the span of all polynomial derivative multiples of its image.
   Prove shift stability, commuting quotient shifts, and group stability from
   an explicit equivariant seed map. This generic covariance is an input for
   arbitrary systems and is proved separately for the physical consumer.
2. Recover the existing scalar symbol relation module and quotient shifts by
   a proved equality/equivalence, without changing or weakening old proofs.
   No homogeneity of an arbitrary equation is silently assumed: fixed grades
   below are actual images, not a claimed global direct-sum decomposition.
3. For specified odd/even systems, form the actual exterior algebra on the
   odd quotient generators tensored with the symmetric algebra on the even
   quotient generators. Construct the projection from the existing mixed
   algebra, prove it onto, and prove even commuting derivatives, group action,
   covariance and projection compatibility. Its kernel is the actual EOM
   kernel, not a supplied relation matrix. A separate noncommutative ideal
   presentation or basis normal-form theorem is not required by this endpoint.
4. Image grades inherit finite-dimensionality for finite component/direction
   sets. Derivatives and the actual divergence range give IBP coefficient
   descent. Compare EOM followed by IBP with the off-shell kernel plus actual
   IBP range in both directions, including equivariance and representative
   formulas. Preserve the local-coinvariant/finite-residual evaluation interface
   for any constructed product action; do not average a local Lorentz group.

## Physical Consumer And Controls

Use one free massless left-chiral Weyl field with the existing SL(2,ℂ)
fundamental component action and the existing dual four-direction action.
Derive the two first-order source equations from the inverse Pauli map and
prove their actual Lorentz covariance (equation indices carry the opposite
dual spin action). Fix their explicit coordinate formulas and normalization;
equation generators are source vectors, while physical coefficients are duals.
Do not equate a source-vector column transformation with a classical field
equation without this convention statement.

The relation module includes every polynomial derivative multiple. Show the
displayed first-order generators and descendants vanish, the scalar wave
descendants follow, and a null-symbol polarization probe detects nonzero jets
of arbitrarily high order before IBP. Instantiate the odd on-shell algebra,
its actual projection and finite EOM/IBP coefficient/source comparison. Scalar
spectators may be included through the common even interface. The nonzero
control concerns generators/algebra before IBP, not a claim of a nonzero
one-field Lorentz-invariant integrated operator.

## Routes And Stops

Primary route: polynomial multiplication on the existing jet presentation,
quotient generators, free exterior/symmetric functors, image grades and
surjective projection transport. For Weyl covariance use the actual inverse
Pauli intertwining identity and finite basis expansion. Fallback: the same
source and equation map through the tensor/Hom duality presentation; do not
replace physical covariance by an assumption. Failed actual-source or Weyl
covariance connection within these routes is a documented scoped stop, not
a new external premise or an automatically expanded foundation project.

Retain dependency pins, default heartbeats and recursion/kernel limits.
Heavy checks are serialized, four Lean threads, 540-second timeout and a
16 GiB per-process inherited address-space guard. Require strict persistent
transitive audits (standard axioms only), focused builds and full `lake build`,
layout/aggregate registration, local links, topic/metadata/diff checks, source
and assumption reconciliation, review and commit. A checkpoint commit is not
a stopping condition. Stop successfully after these gates; no master merge or
push is authorized. The child may remain verified and unmerged for review.

Excluded: right/conjugate or massive/interacting Weyl EOM, gauge-covariant
commutators and Bianchi identities, analytic/variational actions, amplitude or
momentum-basis equivalence, full EFT tables, UV matching, rates, numerical
dynamics and general algebraic-group saturation. No literature completeness
or physical matching input is imported. A general system theorem proves an
implication; only the actual physical instantiation discharges its covariance.

## Source/Dual Convention Reconciliation

During implementation, the Weyl seed is fixed as the **dual Pauli contraction**
followed by the first-jet frame, rather than substituting the inverse Pauli
coordinate matrix as a source relation. This corrects the initial construction
description above: the coefficient space is dual to the source, so inverse
and transpose roles must not be interchanged. The equation parameter is the
dual right spinor and its actual intertwining is proved. The physical scope,
source, hypotheses and acceptance gates stay as specified; no covariance or
completeness premise is added. Tensor/Hom transport remains the alternate
presentation of this same map.
