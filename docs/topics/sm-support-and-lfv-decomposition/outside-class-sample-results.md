# Samples Beyond Scalar/Abelian Residual Actions

## Outcome

The two routes in the [contract](outside-class-sample-contract.md) are complete.
Three concrete samples were tested: common S3 generation permutations, common
A4 sum-zero generation action, and a signed SU(6) color/weak exchange. None
provides a protecting model. These tests suggest useful *screening* patterns;
they do not support exhaustive SU(6) classification.

| Sample | Actual certificate | Outcome | Remaining realization boundary |
| --- | --- | --- | --- |
| S3 permutation action on three generation coordinates | Noncommuting represented generators; actual SU(6) tensor source and standard-gauge branching; nonzero physical qque exterior coefficient | Common non-Abelian flavor does not forbid qque on these participating species | An invariant mass/VEV and its exact light radical are not constructed |
| A4 sum-zero action on four coordinates, dimension three | Noncommuting represented generators; actual SU(6) tensor source and branching; no invariant flavor functional but nonzero physical qque coefficient | Absence of single-factor invariants does not forbid a four-field coefficient | Same mass/VEV/radical boundary; no irreducible-decomposition classification needed |
| Signed exchange of color coordinate 0 and weak coordinate 3 | Actual SU(6) element, actual embedded color probe, forbidden cross-entry after conjugation | Cannot implement a normalizing action on this standard SM image | Rejected before mass, VEV or coefficient construction; other embeddings are untested |

These are new qque/embedding applications of existing tools. The S3/A4 groups
and their representations were already used in flavor/LFV controls; the
physical qque tests and SU(6) tensor-source branching are the new connections.
No non-Abelian residual group is replaced by scalar charge labels.

## Non-Abelian common-flavor construction

[NonabelianResidualSamples](../../../GUT/SU6/SelectionRules/Models/NonabelianResidualSamples.lean)
constructs the actual algebraic representation

    (15 + 2 bar6) tensor V

of SU(6) x H, using the checked `StandardSMUVFields.uvRho` and an actual
flavor representation. The homomorphism restricting SU(6) to the standard SM
cover is constructed. `branching` gives an equivariant equivalence with the
existing complete gauge decomposition tensored with V. For both samples the
source dimension is 81. This carrier includes the old spectator components;
81 is not a claimed light-spectrum dimension. The sample extension does not
claim a bundled unitary/continuous model or infer an exact radical from branching.

[NonabelianQqueSamples](../../../Physics/StandardModel/Operators/NonabelianQqueSamples.lean)
applies the existing common-factor split pairing and its actual fermionic
alternation witness. `common_flavor_left_species` explicitly transports from
the duals of left-handed uc/ec fields to the physical right-handed carriers.
Thus it does not assign right-handed flavor independently of the left-handed
source. The selected physical species are the ones in the standard branching.
No mass-radical map from the full UV tensor carrier is manufactured.

S3 uses `S3DipoleSelection.action` on C^3. A4 uses
`FiniteFlavorControls.a4` on the sum-zero subspace of C^4. Noncommutation is
proved for the represented linear maps, not only for the abstract groups.
For A4, every invariant linear functional is zero but the qque coefficient
is nonzero. This illustrates why tensor/symmetric constituents, not individual
factor invariant functionals, determine coefficient support.

The general sample pattern is already a consequence of the existing matched
split theorem: a nonzero common flavor factor in participating Q/uc/ec
species supplies a qque witness, even for a non-Abelian group. These samples
do not discover a new independent obstruction or prove that arbitrary
non-Abelian actions on an unknown SU(6) radical have such a common factor.

## Noncommuting color/weak exchange gate

[ColorWeakNormalizerSample](../../../GUT/SU6/SelectionRules/Models/ColorWeakNormalizerSample.lean)
uses the determinant-one signed representatives exchanging (0,3) and (0,2).
The latter is proved to belong to the actual standard SM image by an explicit
SU(3) color matrix and neutral weak/hypercharge components.

Every standard SM image matrix has entry (3,2)=0. Conjugating the color probe
by the (0,3) representative instead yields entry (3,2)=-1. Consequently no
SM-cover homomorphism beta can satisfy the required normalization relation
for this candidate. The result holds before choosing a scalar vacuum or mass;
it is not an exclusion of every inner action outside the SM image.

The exact standard-library Python [probe scan](../../../tools/su6-twisted-protection/check_sm_block_probes.py)
enumerates all 720 coordinate permutations with determinant-one signed
representatives. Four color/weak signed probes reject 708; the 12 passing
representatives are precisely the ones preserving the 3+2+1 coordinate blocks
in this finite scan. It also checks the sample's matrix order four and the
Lean cross-entry value. This is a reproducible computational cross-check,
not a Lean normalizer classification, a continuous-group classification or a
protection certificate for the 12 survivors. Diagonal phases are not enumerated.

## What this suggests next

The present samples justify two early checks: actual SM-image normalization
before VEV/mass work, and non-Abelian tensor/common-factor support before
scalar-character reasoning. Merely replacing a scalar residual group by a
common S3/A4 flavor action does not create protection in these samples.

Different representations on different species, actions induced by genuinely
different embeddings, outer actions and antilinear actions are untested here.
In particular, the Abelian profile theorem is not silently applied to S3/A4.
Further work should first select an action that passes normalization and avoids
the existing matched-factor witness, then determine its actual light-field
dictionary. These samples give no evidence that such a SU(6) realization exists.
Full SU(6) classification remains outside the authorized endpoint.

## Verification

The [verification record](verification.md) records strict transitive audits,
focused/full builds, the three Python checks and layout/document checks.
No dependencies, heartbeat limits, axioms or audit exceptions were changed.
No master merge or push is authorized.
