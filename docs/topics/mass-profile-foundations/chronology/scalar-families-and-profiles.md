# Scalar families and charge profiles

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

- Planned the next extensions, candidate 1 before candidate 2:
  equivariant scalar-dependent mass coefficients, finite higher-degree
  constructions and their existing-endpoint adapter; then finite charge
  profiles, actual radical support, and source-derived SU(6) assembly with
  SU(5) compatibility. ACTIVE contains the six pending milestones; the
  [stable plan](../plans/MASS_AND_FLAVOR_EXTENSION_PLAN.md) distinguishes
  shared algebra from group-specific source bridges and preserves all
  checked scopes. This is documentation only, not a new proof or build.
- Completed MASS-1: `InvariantMassData` extracts the old symmetric mass,
  invariant vacuum, and stabilizer primitives without changing their names.
  `WeylMassFamily` constructs fixed-vacuum masses for arbitrary equivariant
  scalar-dependent coefficients and arbitrary subgroup homomorphisms. The
  separate compatibility adapter proves exact equality with old linear
  masses. Persistent audits exclude SU(5)/SU(6) imports from the core,
  refute dropping the fixed-vacuum premise, and check nonlinear, constant,
  zero-vacuum, and nontrivial stabilizer examples. Targeted build 3841 jobs,
  22 standard-axiom reports; full regression 4367 jobs. No new axioms or
  dependency changes. ACTIVE now starts at MASS-2; the physical-model
  extension and finite charge-profile work remain targets. See
  [the mass-family dossier](../../../proof/current/inputs/Physics/SCALAR_DEPENDENT_MASS.md).
- Completed MASS-2: finite complex multilinear coefficients and covariant
  real-linear slots construct equivariant mass families, including repeated,
  mixed, and conjugate slots. A real multilinear diagonal and homogeneous
  scaling law precisely record the polynomial source class; no claim of
  holomorphicity is made for conjugate slots. Finite sums, degree-zero/one
  recovery, positive-degree zero-vacuum laws, joint continuity, and exact
  old subgroup-mass recovery are checked. Persistent audits build a charged
  nonzero stabilizer mass and mixed/conjugate examples, reject SU(5)/SU(6)
  imports from the core, and print standard axioms only. Targeted build:
  3844 jobs, 51 axiom-bearing reports across three audits; full regression:
  4370 jobs, 1300 standard-axiom reports. Dependencies are unchanged. ACTIVE
  now starts at MASS-3; no physical-model endpoint or selection-rule scope
  is enlarged yet. See the [family dossier](../../../proof/current/inputs/Physics/SCALAR_DEPENDENT_MASS.md).
- Completed MASS-3: `ContinuousWeylFamilyModel` derives the mass from a
  jointly continuous equivariant family and fixed vacuum, then composes
  with the existing scoped SU(6) endpoint. The old linear model converts
  without a new continuity certificate, preserving the full mass model
  and light spectrum. Actual finite neutral power coefficients recover
  the nonzero 15-mode benchmark at VEV one; degree two is nonadditive.
  The same nonzero coupling at zero VEV gives zero mass and a whole-space
  radical. Actual supported signatures and finite Abelian specialization
  are audited. Targeted build: 4177 jobs, 55 standard-axiom reports; full
  regression: 4374 jobs, 1328 standard-axiom reports. Dependency pins and
  existing APIs are unchanged. The scope is `CompactTorus x H` with the
  exact dual light target retained, not full-gauge mass invariance or a
  dynamically selected vacuum. MASS-1 through MASS-3 close candidate 1;
  ACTIVE now starts at PROFILE-1. The temporary working checkpoint was
  replaced by the [model dossier](../../../proof/current/applications/GUT/SCALAR_DEPENDENT_MODEL.md)
  and [formalization record](../../../proof/current/applications/GUT/interfaces/scalar-dependent-model.md).
- Completed PROFILE-1: five nonnegative finite charge distributions with
  common positive totals, complete SM target coefficients, charge-forgetting,
  and exact old fixed-charge recovery. Optional orbit-profile equalities
  yield occupied neutral charges and paired formal operator signatures.
  The old fifteen-weight target algebra was extracted to `FiniteSMTarget`
  with declaration names/import compatibility preserved. The new profile
  core has a transitive SU(6)-free audit. Actual order-two/three characters,
  distinct/repeated charges, zero-total exclusion, and an incompatible
  correct-total family are kernel-checked. Targeted build: 3944 jobs and
  25 standard-axiom reports; full regression: 4378 jobs and 1353 reports,
  only `propext`, `Classical.choice`, and `Quot.sound`. Existing SU(5)/SU(6)
  endpoints and dependency pins are unchanged. ACTIVE now starts at
  PROFILE-2: target support is not yet actual radical support, and
  PROFILE-3 must derive equal profiles from the source. See the
  [profile dossier](../../../proof/current/inputs/GUT/FINITE_CHARGE_PROFILES.md) and
  [declaration record](../../../proof/current/applications/GUT/interfaces/finite-charge-profiles.md).
- Completed PROFILE-2: shared dual-index coefficient algebra gives actual
  radical multiplicity lower bounds from the family-dependent target.
  `ProfileZeroModeSupport` constructs nonzero vectors at every occupied SM
  weight and pairs of neutral signatures conditional on orbit equalities.
  It assumes neither eigenvectors nor radical support. Persistent controls
  cover two-torsion, vectorlike pairs, invisible singlets, and negative
  signed support without positive support. The actual nonzero 15-mode and
  26-mode legacy models exercise the new adapter. Targeted build: 4166 jobs,
  48 axiom-bearing reports; full build: 4383 jobs, 1376 reports, only the
  standard three axioms. Old endpoints and pins are unchanged. ACTIVE now
  starts at PROFILE-3's actual-source assembly. See the
  [actual-support dossier](../../../proof/current/applications/GUT/PROFILE_ZERO_MODES.md).
- Completed PROFILE-3a: actual SU(6) dual-index conservation, charge-forgetting,
  hypercharge rigidity, and Weyl-invariant source profiles compose with
  actual radical support. `ContinuousProfileModel` has no orbit-equality or
  support field. Positive legacy mass/spectrum compatibility and MASS-3
  scalar-family composition are checked, including the nonlinear nonzero
  15-mode example and exclusion of the incompatible profile negative control.
  Targeted build: 4187 jobs / 43 reports; full build: 4386 jobs / 1394 reports,
  only the standard axioms. PROFILE-3b (SU(5) adapter) and PROFILE-3c (actual
  nonuniform SU(6) example) remain active; the overall milestone is partial.
  See [the source dossier](../../../proof/current/applications/GUT/PROFILE_MODEL.md).
- Completed PROFILE-3b: generic full character-eigenspace multiplicities
  give finite natural profiles with total dimension, without assuming a
  finite residual group. The actual SU(5) retained-matter adapter derives
  both orbit equalities and preserves field intertwiners and ordered
  invariant tensors. The SU(6)-free audit covers actual generation mixing,
  repeated characters, and zero generations. Targeted build: 3906 jobs /
  48 reports; full build: 4389 jobs / 1411 reports, only the standard axioms.
  PROFILE-3c's actual nonuniform SU(6) example remains. See the
  [SU(5) profile dossier](../../../proof/current/inputs/GUT/SU5_CHARGE_PROFILES.md).
- Completed PROFILE-3c: two actual scalar-charged SU(6) `15 + 2 bar6`
  copies have the derived two-charge SM dual target for every invariant
  symmetric mass. The explicit order-two residual example is not a pure
  fixed-charge target; both charges have actual radical vectors at every
  SM weight. The zero-mass example retains 54 modes and does not claim a
  pure SM spectrum. Targeted build: 4173 jobs / 26 reports; full build:
  4392 jobs / 1437 reports, only the standard axioms. The nonlinear
  nonzero-mass regression and all prior endpoints are preserved. Both
  agreed extension candidates are complete in scope; ACTIVE has no pending
  items. See [the example dossier](../../../proof/current/applications/GUT/NONUNIFORM_PROFILE_MODEL.md).
