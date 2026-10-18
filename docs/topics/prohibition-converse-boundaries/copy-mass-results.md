# Exact Copy Conditions for Existence of an SM Radical

For the actual full-SM restriction of the fixed 10/bar5/40/50 family and its
algebraic duals, any natural counts p,q and any N satisfy

    exists symmetric SM-invariant mass with radical equivariant to N SM generations
    iff (p0-q0,p1-q1,p2-q2,p3-q3) = (N,N,0,0).

The first two differences are integers. N=0 is included. The group is the
existing full SM covering group with no additional residual generation action.
The previous necessity proof is reused; it is not a dimension-only assumption.

For sufficiency, rewrite positive counts as (N+q0,N+q1,q2,q3). Proved copy-sum
representation equivalences identify source p with N copies of the actual
10+bar5 SM-generation representation plus source q. Reassociate the unchanged
original fields into SM light fields plus source q and its dual, construct
the existing symmetric evaluation-pair mass, and pull it back equivariantly.
Its radical is explicitly equivalent to the declared SM generations.

The [source](../../../GUT/SU5/SelectionRules/ActualFullFamilyMassExistence.lean)
provides sourceSplit, counts_positive, exists_mass_of_counts and exists_mass_iff.
[CopySumEquivalence](../../../Math/RepresentationTheory/Multiplicity/CopySumEquivalence.lean)
is reusable for arbitrary finite copies, representation products and regrouping.

The zero_mass_control fixes q=(1,0,0,0) and p=(2,1,0,0), N=1. A suitable mass
exists, but the invariant zero mass does not have that SM radical. The extra
nontrivial vectorlike sector remains light. This separates existence of some
mass from an assertion about every mass with consistent counts.

The [contract](copy-mass-contract.md) is complete. No SU(5)-invariant UV mass,
VEV realization, additional residual protection or physically generated mass
spectrum is certified. The existing gauge-only qque no-go remains applicable
when positive-generation SM light content is present.
