# Whole DUQL Content: All-Higgs Support Criterion

## Proved result

For the actual three-generation signed SM/Weyl input with one each of D,U,Q,L,
neutral one-copy Higgs and algebraic dual-Higgs fields, every positive cyclic
order k and universal physical charges (q,q,q,l,l), the full fixed-content
coefficient space at Higgs counts h,a satisfies

    nonzero coefficient exists iff h=a and 3q+l=0 mod k,
    every coefficient is zero iff h!=a or 3q+l!=0 mod k.

Consequently prohibition at every Higgs count for this DUQL content is
equivalent to 3q+l!=0. This does not classify every B1 fermion content.

[DuqlHiggsContent](../../../Physics/StandardModel/Operators/DuqlHiggsContent.lean)
defines Space by species support on the existing actual invariant
exterior-four/symmetric-(h+a) coefficient carrier. It includes every permitted
contraction and flavor coordinate; no seed list or dressing range defines it.
The supported-space projection preserves selected pure values and fixes every
coefficient already in the space. Hypercharge invariance proves h=a, and
actual cyclic actions on each species prove charge neutrality is necessary.

For sufficiency, baseEquiv reconstructs a zero-Higgs DUQL family coefficient
from the previously proved full dictionary. Multiplication by the certified
normalized Higgs invariant gives rawDress. Its species support is proved:
the fermion coefficient vanishes outside DUQL and hypercharge forces balanced
scalar counts. Thus dressed belongs to the whole content space and is nonzero
when a neutral DUQL coordinate exists. This is a genuine existence converse;
it does not assert every coefficient is such a dressing.

The earlier DressedDuqlFamily result classified the image of one dressing map.
The new theorem instead classifies existence in the entire fixed DUQL content,
for unequal as well as equal Higgs counts. It does not assert equality between
that image and the full space. No VEV, semisimplicity premise, mass input,
finite-generation premise or UV realization is added to this physical iff.

## Certified finite-seed consumer

[FiniteSeedEvaluation](../../../Math/LinearAlgebra/FiniteSeedEvaluation.lean)
proves the bridge suggested by the literature. Given an explicit R-span
certificate and a K-linear evaluation compatible with a ring homomorphism
chi:R->K, its image equals the K-span of the evaluated seeds. A linear target
test vanishes on all evaluations iff it vanishes on every evaluated seed.
Separately, an R-linear operator-level test has the same vanishing criterion.
The proofs work for any index set; a finite certificate gives a finite test.

The span equality and evaluation compatibility are explicit parameters, not
custom axioms or discharged invariant-theory inputs. This consumer does not
construct the actual Higgs invariant ring or a complete seed list. A fixed
vacuum test remains different from graded operator support.

## Remaining finite-spanning gate

The planned finite-generation milestone is not proved. In particular, neither
C[t] as the full scalar invariant ring nor generation of all mixed DUQL
covariants by degree-(0,0)/(1,1) seeds is certified. No minimal generator count,
full coefficient-space dimension or free-module structure is claimed.
The exact support result above avoids these premises because the necessary
obstructions and an actual nonzero witness already meet for this content.

The further source inspection found useful TauCeti SU2 weight bases and a
character recursion, but not the required actual all-degree intertwining
Clebsch--Gordan equivalence or covariant multiplication surjectivity. The
Completeness file explicitly distinguishes its character identity from the
representation decomposition. Thus character identities were not used as
coefficient-spanning premises.

The concrete remaining obligation can be isolated as follows: prove all weak
covariants of the two fermion doublets and H/H-dual are spanned by low-degree
singlet/triplet contractions times powers of the scalar pairing, retaining
bidegree and the actual color/Lorentz/flavor/statistics transport. A four-doublet
low-degree certificate and symmetric-power weight basis are starting inputs,
not this uniform theorem. This is a missing concrete certificate, not evidence
that a general reductive invariant-theory library is indispensable.

The continuation stops at the bounded missing-spanning-certificate endpoint.
Its whole-content support and abstract certificate-consumer results are proved;
its finite-generation target remains open. Other contents, full B1 support,
and the 572 assignments/151 orbit classification are unchanged.

## Verification

Both source files are registered in their layer aggregates and the existing
strict audits. The [verification record](verification.md) lists focused and
full builds, strict checks and document/layout checks. Only propext,
Classical.choice and Quot.sound are permitted. No dependency, heartbeat,
custom axiom or audit exception was introduced.

## Subsequent four-family extension

[FourFamilyHiggsContent](four-family-results.md) now includes this DUQL
whole-content result as its zero-index control and proves the same support
iff for QQUE, QQQL and DUUE. This extends the classified contents without
discharging the remaining finite-generation premise.
