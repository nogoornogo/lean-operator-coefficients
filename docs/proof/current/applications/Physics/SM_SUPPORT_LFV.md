# Finite Nonabelian LFV and All-Degree Dressing

## Exact LFV results

[S3DipoleSelection](../../../../../Physics/StandardModel/Operators/Dipole/S3DipoleSelection.lean)
uses the actual permutation action of S3 on C^3. Adjacent-swap relations and
six normal forms are kernel certified; noncommutativity is explicit.
Permutation covariance proves every intertwiner equals a linear combination
of identity and constant coordinate sum. Both maps are actual intertwiners.
For arbitrary mu,ell the actual selected B/W coefficient is allowed iff
ell(mu) or (sum mu)*ell(ones) is nonzero. Vanishing and off-diagonal allowance
are proved without a numerical centralizer or UV model input.

[SemisimpleDipoleSelection](../../../../../Physics/StandardModel/Operators/Dipole/SemisimpleDipoleSelection.lean)
accepts certified source/target equivalences to finite products of irreducible
complex blocks. FiniteBlockHom supplies the rectangular Hom equivalence;
IrreducibleHomScalar uses Schur and actual block bridges; the resulting
IrreducibleBlockCoordinates gives the complete matching-pair coordinate space
and matrix-unit expansion. Selector allowance iff some transported matrix unit
has nonzero evaluation. No Hom basis/spanning premise, common-label equivalence
assumption or generated-coefficient surjectivity is introduced.

[CyclicSemisimpleDipoleControl](../../../../../Physics/StandardModel/Operators/Dipole/CyclicSemisimpleDipoleControl.lean)
certifies scalar irreducibility and the actual decomposition of cyclic diagonal
modules and recovers the prior arbitrary-selector support iff. An explicit S3
trivial/standard decomposition is not assumed or newly certified. A bare
semisimplicity theorem does not automatically compute the required data.

## Actual infinite mixed coefficients

[DressedDuqlFamily](../../../../../Physics/StandardModel/Operators/BaryonOne/OtherFamilies/DressedDuqlFamily.lean)
reconstructs the actual DUQL seed from the flavored dictionary with all other
coordinate factors zero. NeutralHiggsPowers identifies the actual Higgs/dual
field sum and its neutral multiplicities, pulls back an invariant symmetric
evaluation pairing and constructs every symmetric-power coefficient using
InvariantQuadraticPowers. A factorial and 2^r normalization are proved nonzero;
the normalized diagonal polynomial is exactly (H-dagger H)^r.

MixedInvariantDressing forms the actual tensor-product coefficient and proves
nonzero products by evaluations. The linear range of these mixed coefficients
at degrees (4,2r) has allowance iff 3q+l=0, for every natural r and every
positive cyclic order. Nonneutrality makes the DUQL index set empty.
unbounded_allowance proves no uniform scalar-degree cutoff on the neutral
family. This is one certified infinite family, not an all-degree B1 spanning
certificate, generated interaction or amplitude.

## Finite fermion input and the remaining support boundary

[ThreeGenerationFermionBound](../../../../../Physics/StandardModel/Operators/Selection/ThreeGenerationFermionBound.lean)
proves the actual ten signed species dimensions sum to 180. Every exterior
source above degree 180 is zero, hence all actual mixed coefficients there
vanish for arbitrary scalar degree. Nonzero coefficients determine a finite
species-count superset. It is not an admission classifier and has no Higgs
cutoff. The existing odd-fermion Lorentz exclusions remain separate.

The complete fixed-input support theorem is not proved. The
[recorded boundary](../../../../topics/sm-support-and-lfv-decomposition/support-boundary.md)
identifies the missing uniform weak/hypercharge covariant reduction or finite
module-spanning certificate and its local/statistics connection. No all-degree
classification or revised count of the 572 assignments/151 orbits is claimed.
The feasibility stop is not a mathematical impossibility or evidence that a
full general invariant-theory library is unavoidable.

## Verification

Layer-owned [Math audit](../../../../../Math/RepresentationTheory/Constructions/Audit/AuditSMSupportLFV.lean)
and [Physics audit](../../../../../Physics/StandardModel/Operators/Support/Coordinates/Audit/AuditSMSupportLFV.lean)
check all 412 registered declarations transitively under the unchanged standard-three-
axiom policy. Sources and exact reuse roles appear in the
[register](../../../../topics/sm-support-and-lfv-decomposition/references.md).
Builds and checks belong to [verification](../../../../topics/sm-support-and-lfv-decomposition/verification.md).

## Whole fixed DUQL content

[DuqlHiggsContent](../../../../../Physics/StandardModel/Operators/BaryonOne/OtherFamilies/DuqlHiggsContent.lean)
defines the whole fixed species-support space with one each of DUQL, h Higgs
and a dual-Higgs fields. Actual invariance forces h=a and 3q+l=0 for a
nonzero coefficient. A dictionary DUQL witness times the normalized pairing
power lies in that actual content and is nonzero. Thus allowance iff h=a
and 3q+l=0, and all-Higgs prohibition for this content iff 3q+l!=0.
This classifies existence in the full content, beyond a dressing range;
it supplies no full spanning list or all-content B1 theorem.

[FiniteSeedEvaluation](../../../../../Math/LinearAlgebra/Constructions/FiniteSeedEvaluation.lean)
proves evaluated image/span and zero-test reductions from explicit spanning
and scalar-evaluation compatibility certificates. The actual invariant-ring
and seed-generation premises remain unproved. See the
[bounded continuation](../../../../topics/sm-support-and-lfv-decomposition/duql-content-results.md).

## All four fixed contents

[FourFamilyHiggsContent](../../../../../Physics/StandardModel/Operators/Higgs/FourFamilyHiggsContent.lean)
parameterizes the actual fixed-content spaces by DUQL/QQUE/QQQL/DUUE.
Hypercharge and residual necessity are shared, while baseEquiv retains
each actual statistical dictionary. Symmetric QQUE and sorted/Young QQQL
coordinates give actual nonzero seeds when neutral; invariant dressing
yields nonzero coefficients at every balanced Higgs count. Each whole
space has allowance iff h=a and 3q+l=0. Their independently defined union
is prohibited iff each space is prohibited, hence all four are forbidden
at every Higgs count iff 3q+l!=0. Other contents and full finite spanning
are not inferred. See the [result](../../../../topics/sm-support-and-lfv-decomposition/four-family-results.md).

## Generic content support adapter

[ContentHiggsSupport](../../../../../Physics/StandardModel/Operators/Higgs/ContentHiggsSupport.lean)
allows arbitrary fermion degree and species-content predicates on the fixed
three-generation universal cyclic input. Constant actual hypercharge Y and
residual charge c give necessary Y+3h-3a=0 and c=0. For Y=0, a supplied
actual neutral supported exterior seed is dressed and proved nonzero, yielding
allowance iff h=a and c=0. Each of the four families discharges that premise
through its actual dictionary. Divisibility, odd-degree and above-180 controls
exclude actual coefficients. The LL control instead requires h=a+2 and 2l=0.
Unproved seed existence is not a zero-support theorem, and Higgs-dependent
seeds require a further adapter. See the
[result](../../../../topics/sm-support-and-lfv-decomposition/content-adapter-results.md).

## Outside-family adapter trials

[OutsideFamilyHiggsTrials](../../../../../Physics/StandardModel/Operators/Higgs/OutsideFamilyHiggsTrials.lean)
constructs an actual exterior-degree-zero invariant seed and derives a
pure-scalar support iff h=a. A triple-Q input obeying the necessary arithmetic
filters is nevertheless zero by odd-degree Lorentz parity. Actual physical
uR²dR⁴ labels yield necessary h=a and 6q=0; sufficiency is explicitly
conditional on an actual supported six-fermion seed, whose dictionary
transport is not proved here. See the
[trial record](../../../../topics/sm-support-and-lfv-decomposition/outside-family-results.md).

## Six-quark premise discharged

[SixQuarkFullSeed](../../../../../Physics/StandardModel/Operators/BaryonTwo/Coefficients/SixQuarkFullSeed.lean)
constructs an actual local seed through the existing statistical two-coordinate
equivalence. A projection from the full signed field sum onto one flavor of
physical up/down fields has a proved right inverse and physical action
transport. Its common cyclic phase cancels in degree six when 6q=0.
Hypercharge plus projection support certify the exact uR²dR⁴ orbit.
The resulting nonzero SeedSpace element discharges the generic adapter
premise and yields whole-content allowance iff h=a and 6q=0, and all-Higgs
prohibition iff 6q!=0. The previous conditional trial record is superseded
by this actual connection; full B2 support and finite generation remain open.
See the [result](../../../../topics/sm-support-and-lfv-decomposition/six-seed-results.md).

## LLHH shifted all-Higgs support

[WeinbergFullSeed](../../../../../Physics/StandardModel/Operators/Weinberg/WeinbergFullSeed.lean)
constructs an actual supported LLHH coefficient through the physical Weinberg
dictionary and full-field projection/right inverses. Its lepton cyclic
phase cancels when 2l=0. SymmetricCoefficientDressing constructs actual
symmetrized scalar multiplication and covariance, with a product formula
at a common diagonal point. Both LLHH and the invariant Higgs pair powers
have normalized value one there. Actual support/hypercharge transport
certifies every dressing, giving allowance iff h=a+2 and 2l=0 in the
whole two-lepton content, and all-Higgs prohibition iff 2l!=0. No VEV or
mass result is inferred; other contents and finite generation remain open.
See the [result](../../../../topics/sm-support-and-lfv-decomposition/llhh-results.md).

## Restricted eigenline reduction and the weak-doublet boundary

[Eigenline reduction](../../inputs/Math/HIGGS_EIGENLINE_REDUCTION.md) constructs
full symmetric coefficient-space equivalences for actual one-dimensional
scalar representations. Common Higgs/dual pairs cancel; an explicit positive
character period k reduces all-degree support and prohibition iff to k Hom
tests. This mathematical class does not include the actual SM weak doublet.
HiggsEigenlineBoundary proves LL zero-Higgs prohibition and LLHH allowance
when 2l=0, hence rules out their support equivalence despite residual neutrality.
It does not rule out a larger finite primitive set. Complete SM support still
needs the uniform weak-doublet reduction and actual content bridge; neither
is obtained by applying the eigenline result to a Higgs component.

## Actual weak doublet with weak-singlet matter

[Weak-doublet reduction](../../inputs/Math/WEAK_SINGLET_HIGGS_REDUCTION.md)
constructs full coefficient-space equivalences with unrestricted symmetric
Higgs/dual degrees for weak-singlet sources. Actual SU2 irreducibility and
constructed perfect symmetric dual pairing give exhaustive scalar uniqueness,
not merely nonzero dressing. WeakSingletHiggsSupport proves the actual SM
Higgs restriction and weak triviality for uR,dR,eR and signed dual fields,
including every exterior degree. Balanced spaces reduce to zero Higgs and
unbalanced spaces vanish; color, Lorentz, residual and fermion statistics remain
in the zero-Higgs source Hom. This is a split symmetric carrier theorem.
Nontrivial weak sources and the full direct-sum content bridge remain open.
