# A Fixed S3 Flavor Action Allowing Qque

This algebraic sample tests a noncommuting residual flavor action on three
SM generations. It admits bijective invariant flavor maps in the charged
fermion channels and a nonzero actual qque exterior coefficient. It is a
specified input to the coefficient framework, not a constructed UV theory.

## Input and result

The residual group is S3. In physical right-handed conventions, the fixed
flavor dictionary is:

| Fields | Three-dimensional flavor action |
| --- | --- |
| Q, uR, dR | Permutation representation |
| L, eR | Three copies of the sign character |
| Higgs weak doublet | Trivial residual action |

Gauge, Lorentz and flavor actions use the existing independent product
convention. The following statements are proved in Lean for this dictionary:

- Two quark flavor actions do not commute on the actual flavor carrier.
- Each species flavor action commutes with its independent SM gauge action.
- Bijective invariant flavor maps Q→uR, Q→dR and L→eR exist.
- The statistics-constrained physical qque coefficient space is nonzero.

The explicit flavor coefficient is det(ones, x*y, z) times sum(r), where
x,y,z,r belong to Q,Q,uR,eR and x*y is coordinatewise multiplication.
The two Q inputs enter symmetrically. The determinant sign cancels the
lepton sign under permutations, and a basis tuple evaluates to 1. The
existing physical exterior coefficient equivalence transports this witness
to the actual selected qque sector.

## Interpretation and limits

The sample removes the noninjective/zero flavor-map obstruction found in the
[earlier unequal S3 samples](../../topics/sm-support-and-lfv-decomposition/sm-preserving-sample-results.md),
while qque remains allowed. Thus a noncommuting residual action and these
flavor-map gates alone do not imply prohibition of this selected sector.
An allowed coefficient does not establish a generated interaction or rate.

The flavor maps are not a complete physical Yukawa certificate. Their
correspondence with gauge/Higgs/spin Yukawa tensors, realistic masses and
mixing, quantum/anomaly consistency, and UV or SU6 realization are not
established. This result does not classify all B1 sectors or residual groups,
and does not supply the full ten-species signed-field bridge.

Read the [proof dossier](../../proof/current/applications/Physics/EXPLICIT_SM_RESIDUAL_TENSOR.md#s3-sample-passing-bijective-flavor-map-gates)
and [Lean source](../../../Physics/StandardModel/Operators/BaryonOne/Qque/S3YukawaCompatibleQque.lean)
for the precise certificates. The [topic](../../topics/s3-yukawa-compatible-qque/README.md)
retains the plan and stopping decision; its [verification record](../../topics/s3-yukawa-compatible-qque/verification.md)
records builds, strict transitive axiom audits and the exact finite supplement.

The [conditional-input recheck](../../topics/conditional-model-input-check/results.md)
records later restricted consumers and reused certificates, with each model
correspondence and stopping boundary kept explicit.
