# Non-Abelian Light Source Bridge

- ID: nonabelian-light-source
- Status: completed
- Working branch: `proof/nonabelian-light-source`
- Integration target: `master`; user approved merging after the final checkpoint
- Result type: proved nonzero ordered residual internal coefficients for finite H;
  not a full-gauge/Lorentz/Grassmann or amplitude theorem

## Frozen Goal

Extend the structural conjugation argument to finite ordinary residual groups
without assuming commutativity. Retain actual ambient conjugations, commuting
ambient/residual actions, finite-dimensional complex fields, restricted
unitarity, invariant symmetric mass, and positive local light targets. Derive
common constituent compatibility, not assume it. Recover the old Abelian
target as a consistency check. The endpoint is a nonzero ordered internal
coefficient on actual light sectors; not a Lorentz/Grassmann nonvanishing
theorem, generated interaction, decay amplitude or lifetime.

The user initially requested milestone commits without a master merge, then
approved integration after completion. Retain this branch after merging.
Resource interruptions must leave a resumable record; do not replace open
proofs with axioms or silent extra assumptions.

## Work Packages

| ID | Deliverable | State |
| --- | --- | --- |
| NS-1 | Actual torus-weight spaces as residual representations; trace expansion and opposite-weight dual character | Proved at the character level |
| NS-2 | Extract orbit relations from actual mass/conjugation; local positive target and Abelian recovery | Proved; coefficientwise equivalence on the common unitary Abelian domain |
| NS-3 | Common irreducible quotients and matched maps on actual light fields | Proved for finite H |
| NS-4 | Ordered qque/duql coefficients, strict audits and full regression | Proved; see final verification record |

Use the checked torus decomposition with only the torus acting as an Abelian
group. Never apply the Abelian joint eigenbasis to T x H when H is non-Abelian.
The prior quotient and coefficient transport lemmas are available. Do not
start new Lie foundations, non-SU5 embeddings, compact residual group
classification, E6 topology or dynamics without approval.

## Endpoint

All four bounded work packages are closed. Actual conjugations imply target
compatibility, positive targets supply common irreducible quotients, and
evaluation through split projections yields nonzero ordered qque/duql residual
coefficients on actual light fields. Abelian recovery is coefficientwise on
the old actual unitary domain, not merely equality of total dimensions.
See [final results and verification](results.md) and
[the source milestone](source-bridge.md). No new research phase is started.

NS-1 constructs the actual residual H representations on full torus sectors,
their finite trace expansion, a faithful complex coefficient evaluator and
opposite-weight residual-dual characters. `ResidualMassIndex.weight_index_invariant`
applies this to an actual mass radical under ambient conjugation. No finite
H assumption is needed yet. No conjugator action on the radical is assumed.
An isomorphism of dual weight spaces is not claimed: the character-level
identity suffices for the planned character/Hom quotient route.

Earlier NS-1 checkpoint: focused audits passed (3390 jobs, 17 strict checks);
full `lake build` passed (5594 jobs), layout passed (573 modules). Existing
warnings were replayed; new modules are clean. Link/diff checks passed.
Source milestone: `checkpoint 01`. Final verification is in the linked results.
The former merge hold has been lifted by the user. Git ancestry records
integration; retain the topic branch and do not push without separate approval.

## New Sources

- [Actual residual weight spaces](../../../Math/RepresentationTheory/Characters/ResidualWeightSpace.lean)
- [Faithful residual character coefficients](../../../Math/RepresentationTheory/Characters/ResidualWeightCharacter.lean)
- [Actual radical index](../../../Physics/FieldTheory/Mass/ResidualMassIndex.lean)
- [Representation-valued SM target](../../../Physics/StandardModel/Spectrum/NonabelianSMTarget.lean)
- [Actual common light quotients](../../../Physics/StandardModel/Spectrum/NonabelianLightSource.lean)
- [Ordered light coefficients](../../../Physics/StandardModel/Operators/NonabelianLightOperators.lean)
- [Abelian target recovery](../../../Physics/StandardModel/Spectrum/NonabelianAbelianRecovery.lean)

## References

- [Approved bridge assessment](../nonabelian-invariant-audit/bridge-assessment.md)
- [Torus sectors](../../../Math/RepresentationTheory/Characters/UnitaryCharacterProfile.lean)
- [Mass/conjugation bridge](../../../Physics/FieldTheory/Mass/ConjugationMassIndex.lean)
- [Positive quotients](../../../Math/RepresentationTheory/Characters/PositiveCharacterQuotient.lean)
- [Coefficient transport](../../../Math/RepresentationTheory/InvariantPairingTransport.lean)
