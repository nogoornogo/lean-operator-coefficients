# completed extensions and their boundaries

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

## Completed Extensions and Their Boundaries

These former optional follow-ups have reached the stated milestones. Their
explicit exclusions are not completion claims and are not automatically
scheduled work; the linked dossiers retain those boundaries.

1. Complete: `StandardWeylFieldIdentification` proves equality of the two
   actual canonical field constructions at the standard pair.
   `ContinuousWeylMassTransport.ofStandard` preserves the given mass, its
   radical representation, and its full spectrum. `ContinuousWeylFullMass`
   now constructs a continuous-geometry model with nonzero mass and exactly
   15 SM zero modes. The persistent audit checks standard axioms.
2. The scalar-linear Weyl Yukawa/VEV bridge is complete in
   `WeylYukawaMass` and `ContinuousWeylYukawaModel`. Primitive symmetric
   couplings and an invariant VEV derive the mass and feed the scoped assembly. Full-group
   invariant Yukawa tensors, restriction to a vacuum stabilizer, and a
   nonzero full-SU(6) `6 + 6*` tensor are checked. The 15-mode example now
   also has zero bare mass, nonzero Yukawa, and VEV one.
   First proton-tensor milestone complete: `StandardSMGaugeTensor` gives
   nonzero ordered `qque`/`duql` tensors on standard field representations,
   invariant under full `SU(3) x SU(2) x U(1)`. `StandardSMResidualTensor`
   proves their residual transformation laws and applies standard charge-orbit bridge -> Abelian proton-operator neutrality, with
   finite-group positive and negative audits. See the
   [tensor dossier](../../../proof/current/applications/Physics/SM_GAUGE_TENSOR.md).
   General-model boundary: the current mass interface
   only requires torus/residual invariance; add a compatible full gauge
   action/invariant-mass certificate before claiming that stronger result.
   The existing 15-mode mass uses a chosen torus eigenbasis; do not assume
   this same mass is fully gauge invariant. Construct a compatible mass
   first if needed. Lorentz/Grassmann nonvanishing is also still separate.
   A decomposed full-gauge candidate is now checked:
   `StandardSMFullGaugeMass` has 27 fields, nonzero mass, and an actual
   15-dimensional all-left-handed SM radical. `StandardSMRadicalTensor`
   constructs the nonzero tensors on that radical and its dual. Its new
   actual SU(6) lift has neutral residual charges; arbitrary assignments
   need not lift. See the
   [mass/radical dossier](../../../proof/current/applications/GUT/SM_GAUGE_MASS.md).
   The first UV-bridge milestone is checked in `StandardSMGroup`,
   `StandardSMTorus`, and `StandardSMContragredient`: the actual continuous
   covering homomorphism, exact physical-torus compatibility at `(-2,3)`,
   and full-group analytic `6`/`bar6` equivalences. The weak dual is
   explicitly the lepton, and neutral residual actions are compatible.
   `StandardSMExterior` now proves the full `15 = exteriorPower 2 6`
   branching by explicit alternating contractions and proved bijectivity.
   `StandardSMUVFields` assembles the actual analytic `15 + 2 bar6` direct
   product, proves continuity, and identifies it with the decomposed mass
   representation. `StandardSMUVMass` pulls back the nonzero mass and proves
   the exact 15-mode SM radical and nonzero invariant tensors on it.
   The persistent audit checks exterior signs and a zero-mass/27-mode
   negative control, with only standard axioms.
   The compatible canonical-carrier adapter is now constructed:
   `StandardSMOrdinaryFields` proves an actual torus/residual equivalence
   and a continuous SU(6) extension with exact restriction compatibility.
   `StandardSMOrdinaryMass` inserts this mass into `ContinuousWeylModel`
   with nonzero mass and the complete 15-mode SM spectrum.
   `StandardSMContinuousTensor` retains the nonzero invariant tensors on
   that model's actual radical. `AuditStandardSMOrdinaryModel` checks the
   restrictions, witnesses, spectrum, and zero-mass/27-mode negative control.
   This is an existence construction, not an identification of a separately
   specified natural full charge-sector action, nor equality with the
   earlier torus-eigenbasis mass. Such a stronger action identification
   and Lorentz/Grassmann nonvanishing remain separate optional extensions.
   The ultraviolet scalar/VEV existence bridge is now checked in
   `SymmetricScalarYukawa`, `ContinuousSymmetricScalar`,
   `UnitarySymmetricScalar`, and `StandardSMUVYukawa`. Symmetric bilinear
   forms on the actual UV matter give a continuous unitary scalar model
   and a full-SU(6)-invariant evaluation Yukawa family, independent of the
   mass choice. A constructed nonzero SM-fixed VEV with zero bare mass
   recovers exactly `StandardSMUVMass.mass`; `ordinary_form` retains the
   canonical-carrier pullback. The audit verifies nonzero coupling and
   mass, 15 modes, finite-Abelian neutral actions, and zero VEV leaving
   27 modes. This nonminimal existence result does not prescribe Higgs
   content, supply a potential or a dynamically selected VEV. The following
   stabilizer audit refutes equality with SM for this particular VEV.
   See [the branching dossier](../../../proof/current/inputs/GUT/SM_BRANCHING.md) for exact declarations.
   See [the Yukawa dossier](../../../proof/current/inputs/Physics/WEYL_YUKAWA.md). No amplitude premise
   or general Lagrangian semantics is claimed.
3. The first stabilizer audit is complete in `StandardSMUVStabilizer`:
   `signedTranspositionSU 0 3` mixes one color and one weak coordinate,
   lies outside `StandardSMGroup.hom.range`, and fixes the existing
   `StandardSMUVYukawa.vacuum H`. The proof derives the original mass's
   coordinate formula, proves its invariance, then uses the actual scalar
   model's fixed-VEV criterion. `standard_lt_stabilizer` proves strict
   containment, not just lack of an equality proof. The permanent audit
   retains nonzero mass and 15 modes and checks standard axioms and finite
   Abelian neutral examples. See [the stabilizer dossier](../../../proof/current/inputs/GUT/SM_VACUUM_STABILIZER.md).
   The full stabilizer is not classified. An exact-SM vacuum would require
   different or additional scalar data and a new proof; equality for the
   unchanged VEV is not a remaining task. The scoped assembly and older constructions remain
   unchanged. Potential dynamics and amplitudes are not addressed.
