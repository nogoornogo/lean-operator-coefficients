# completed mass source extensions

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

## Completed Mass-Source Extensions

- **MASS-1: equivariant scalar-dependent coefficients (stage 01).**
  Arbitrary equivariant families of symmetric bilinear forms now produce
  invariant masses at a fixed vacuum, also after restriction along any
  group homomorphism. Scalar-linearity, commutativity, finite dimension,
  unitarity, and topology are not needed for this algebraic result.
  Extracted the minimal mass/vacuum primitives with their old names intact;
  the new core's transitive imports exclude SU(5) and SU(6). The separate
  legacy adapter proves exact equality with the old scalar-linear masses.
  Persistent controls include a non-fixed-vacuum counterexample, a
  nontrivial surviving stabilizer action, zero mass from a nonzero coupling,
  genuinely nonadditive scalar dependence, and a constant family's nonzero
  zero-vacuum mass. Targeted build 3841 jobs, 22 standard-axiom reports;
  full regression 4367 jobs. Both audits are in the root build. No new
  axioms or dependency changes. At this checkpoint MASS-2/MASS-3 remained
  targets, and neither
  final GUT theorem's scope has changed. See the
  [proof dossier](../../../proof/current/inputs/Physics/SCALAR_DEPENDENT_MASS.md) and
  [declaration record](../../../proof/current/inputs/Physics/interfaces/scalar-dependent-mass.md).

- **MASS-2: finite multilinear scalar sources (stage 01).**
  `MultilinearWeylMass` derives equivariant families from finite complex
  multilinear coefficients and covariant real-linear slots. Repeated,
  mixed, and conjugate slots are covered without a holomorphicity claim.
  With compatible scalar actions, the family is the diagonal of a real
  multilinear map with a proved homogeneous scaling law. Finite sums,
  constant/linear recovery, positive-degree zero-vacuum behavior, and
  exact legacy subgroup-mass recovery are checked. Finite-dimensional
  coordinate expansions give joint scalar/fermion continuity.
  Persistent controls construct powers, mixed/conjugate coefficients,
  constants plus positive-degree terms, and a charged nonzero stabilizer
  mass. The generic import closure excludes SU(5) and SU(6).
  Targeted build: 3844 jobs, 51 standard-axiom reports across three audits;
  full regression: 4370 jobs, 1300 standard-axiom reports. No new axioms or
  dependency changes. At this checkpoint the wrapper remained MASS-3; neither
  final GUT theorem is enlarged at this milestone. See the
  [proof dossier](../../../proof/current/inputs/Physics/SCALAR_DEPENDENT_MASS.md).

- **MASS-3: scalar-dependent model endpoint (stage 01).**
  `ContinuousWeylFamilyModel` derives an invariant mass from a jointly
  continuous equivariant coefficient and fixed vacuum, then reuses the
  existing hypercharge, charge-neutrality, and actual-support endpoint.
  Every old linear model converts without extra continuity input and with
  exact mass-model/light-spectrum equality. The generic finite neutral
  coefficient has diagonal `s^n B`; VEV one recovers B. Its quadratic
  realization recovers the nonzero 15-mode continuous benchmark, with
  proved nonadditivity and an actual supported signature. Keeping the same
  nonzero coefficient but setting the VEV to zero gives zero mass and a
  whole-space radical. Finite Abelian specialization is audited too.
  Targeted build: 4177 jobs, 55 standard-axiom reports; full regression:
  4374 jobs, 1328 standard-axiom reports. No new axioms or dependency changes.
  This is the existing `CompactTorus x H` interface with its exact-index
  hypothesis, not new full-SU(6) scalar geometry or vacuum dynamics.
  MASS-1 through MASS-3 close candidate 1; at this checkpoint PROFILE-1 was next. See the
  [model dossier](../../../proof/current/applications/GUT/SCALAR_DEPENDENT_MODEL.md) and
  [declaration record](../../../proof/current/applications/GUT/interfaces/scalar-dependent-model.md).

- **PROFILE-1: finite SM charge distributions (stage 01).**
  `FiniteChargeProfiles` supplies five natural finite distributions with
  common positive totals, an integer resolved target with independent
  singlet index data, exact coefficients at all fifteen SM weights,
  charge-forgetting, and equality with the old fixed-charge target in the
  pure case. Separate orbit-profile equalities yield occupied neutral
  charges and both formal invariant target signatures. They are not built
  into the family definition. The old target algebra now lives in
  `Physics/StandardModel/Spectrum/FiniteSMTarget`, retaining its declaration names and old
  SU(6) import entry point. The new core has a checked SU(6)-free closure.
  Audits cover actual order-two/three residual characters, repeated and
  distinct generation charges, zero-total exclusion, and correct-total
  profiles with neither signature neutral. Targeted build: 3944 jobs,
  25 standard-axiom reports; full regression: 4378 jobs, 1353 reports,
  only the standard axioms. No dependency or toolchain changes.
  Target support is not actual radical support: PROFILE-2/3 remain, and
  no existing physical-model endpoint has been enlarged. See the
  [profile dossier](../../../proof/current/inputs/GUT/FINITE_CHARGE_PROFILES.md) and
  [declaration record](../../../proof/current/applications/GUT/interfaces/finite-charge-profiles.md).

**PROFILE-2 actual profile zero modes (stage 01)**.
The dual target gives a coefficient lower bound at every occupied SM key;
faithful actual character evaluation and nonnegative radical multiplicities
then construct nonzero massless eigenvectors at all fifteen weights.
Conditional orbit equalities give both neutral signatures on the actual
radical spectrum. The old duality algebra is extracted without changing
declaration names. Torsion, extra conjugate pairs, invisible self-dual
singlets, and wrong signed orientation are audited. Nonzero-mass 15-mode
and 26-mode legacy examples both pass the new interface. Targeted build:
4166 jobs / 48 standard-axiom reports (including PROFILE-1); full regression:
4383 jobs / 1376 reports, only the standard axioms. Source-derived final
assembly remains PROFILE-3, not a new assumed orbit/support field.
See [the dossier](../../../proof/current/applications/GUT/PROFILE_ZERO_MODES.md).

**PROFILE-3a source-derived profile endpoint (stage 01)** is checked.
`PhysicalProfileSource` derives hypercharge from charge-forgetting and the
same actual dual target, then uses source Weyl invariance to derive the
profile equalities. `ContinuousProfileModel` composes those results with
actual radical support. No profile equality or support is a model field.
Positive legacy masses/spectra are preserved; the scalar-family wrapper
retains the nonlinear nonzero 15-mode benchmark. Targeted build: 4187 jobs,
43 standard-axiom reports; full regression: 4386 jobs, 1394 reports, only the
standard axioms. The SU(5) adapter and actual nonuniform-charge example
remain PROFILE-3b/3c, so the overall PROFILE-3 milestone is not yet complete.
See [the source dossier](../../../proof/current/applications/GUT/PROFILE_MODEL.md).

**PROFILE-3b actual SU(5) profiles (stage 01)** is checked.
Full character eigenspace dimensions give finite natural distributions with
the actual generation total. Every occupied assignment retains the existing
SM field maps; a compatible one gives the nonzero invariant ordered tensors.
The residual group need not be finite. The SU(6)-free audit covers mixing,
repeated characters, and zero generations. Targeted build: 3906 jobs / 48
reports; full build: 4389 jobs / 1411 reports, only the standard axioms.
PROFILE-3c's actual nonuniform SU(6) example remains. See the
[SU(5) profile dossier](../../../proof/current/inputs/GUT/SU5_CHARGE_PROFILES.md).
