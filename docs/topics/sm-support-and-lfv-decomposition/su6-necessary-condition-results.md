# Bounded Necessary-Condition Extraction Results

## Endpoint

Both routes in the [plan](su6-necessary-condition-plan.md) have reached their
bounded endpoint. The first supplies a mixed-pair necessary condition and an
actual coefficient control. The second extracts an arbitrary-character target
exclusion from the existing SU(6) standard-chain theorem. Neither constructs
a protecting SU(6) model or proves a new independent SU(6) no-go class.

## Mixed pairs on actual flavored SM coefficients

[MixedQqueCyclicNecessity](../../../Physics/StandardModel/Operators/MixedQqueCyclicNecessity.lean)
uses the existing exact flavored exterior coefficient dictionary. For any
positive cyclic order and finite flavor sets, prohibition of the actual qque
sector implies, for every Q pair i,j and up/electron indices a,b,

    q(i) + q(j) + u(a) + e(b) != 0 mod k.

Here u,e are physical right-handed charges, as in the imported coefficient
dictionary. `neutral_pair_allowed` proves existence of a nonzero actual
coefficient if this sum vanishes. `total_necessary` extracts the same condition
from prohibition of the actual signed dimension-six DeltaL=1 sector containing
the four BNV families. The existing symmetric-pair basis handles statistics;
no nonzero raw tensor or nonzero seed is assumed.

The three-generation k=3 control has q=(0,1,0), u=(0,0,0), e=(2,2,2).
Every diagonal pair test fails neutrality, but the pair (0,1) is neutral.
`control_allowed` and `control_total_allowed` prove actual qque and full signed
sector allowance. Thus diagonal-pair filtering misses a genuine coefficient.
This does not claim that every abstract invariant-subspace `Triplet` has been
classified. Nor is it a new mathematical obstruction beyond the existing
flavored completeness theorem: it extracts that theorem for input filtering.
The control certifies SM species and gauge action, not Yukawa compatibility,
anomaly freedom, a mass radical dictionary or an SU(6) lift.

## Arbitrary-copy and arbitrary-mass SU(6) extraction

The frozen admitted class is any actual finite-dimensional complex unitary
representation R of SU(6) times a commuting Abelian group H, with the existing
standard (-2,3) torus restriction, and any invariant symmetric complex-bilinear
mass B on that restriction. This includes arbitrary natural copies of the
existing 15/bar6 carriers and their duals whenever constructed as such an
actual ambient representation; no copy bound or particular mass is imposed.
Rather than introduce a narrower family with assumed branching data, the
existing arbitrary-representation theorem supplies the stronger interface.

The requested target remains a *pure* N-generation chiral dual index, N>0,
with arbitrary singlet index. It need not be an exact radical spectrum.
In [PhysicalIndexObstruction](../../../GUT/SU6/SelectionRules/Models/PhysicalIndexObstruction.lean),
`pure_qque_neutral` derives

    chi_Q^2 * chi_uc^(-1) * chi_ec^(-1) = 1.

`no_pure_nontrivial_target` therefore excludes every such target whose qque
character is nontrivial, for arbitrary genuine H characters. Unlike the older
named search consumer, it is not restricted to five Z5 assignments.

This is an explicit extraction of the already proved equalities Q=uc=ec;
it adds no independent SU(6) exclusion mechanism. It requires no actual
light-field decomposition, but consequently does not manufacture one either.
A claim about prohibition in the full physical coefficient domain still needs
the actual light-field dictionary and restriction to the participating carrier.
The mixed-pair control above is not asserted to arise in this ambient class.

## What the new Higgs connection contributes here

The full Higgs constituent equivalence remains available for every h,d, but
these two extractions already operate at zero Higgs degree. No further
Higgs-dependent SU(6) exclusion has been proved. Classifying the remaining
source/constituent Hom support would be a separate theorem-level prerequisite;
the bounded plan does not silently reopen it.

Generation-dependent non-pure profiles, additional allowed residual actions,
alternative embeddings and full UV realization retain their boundaries.
The user reserved new residual-action classes for a later decision. No
derivatives, quantum protection, matching or decay-rate claim is made.

## Verification

See the [verification record](verification.md). The strict audits cover every
new declaration and its transitive axioms. No pins, heartbeat limits, custom
axioms, placeholders or audit exceptions were changed. No merge or push is
authorized by this endpoint.
