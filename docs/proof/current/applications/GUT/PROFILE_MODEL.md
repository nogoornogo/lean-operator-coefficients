# Source-derived profile model endpoint

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

### Checked Scope

**LEAN-CHECKED: PROFILE-3, including all acceptance gates.**
`ContinuousProfileModel.Model` extends the
positive-orientation continuous SU(6) symmetric-mass interface from one
charge per species to finite nonnegative charge distributions with common
positive totals. Actual matter is a nonnegative finite sum of continuous
unitary SU(6) representations with a strictly commuting ordinary Abelian
residual action. The invariant symmetric mass is arbitrary.

Its infrared condition remains an **exact dual chiral-index target**, now
built from those profiles and independent singlet index data. It is not an
exact full massless-spectrum assumption. Neither profile equality, a
standard hypercharge pair, nor operator support is a model field.

## 4. Proof structure

### Derived Chain

1. Conservation of the mass radical's dual trace transports the infrared
   target to the actual ultraviolet source. Faithfulness gives a physical
   charge-resolved polynomial identity.
2. Forgetting residual charges gives the ordinary SM target with the common
   positive generation count. The existing fifth-moment theorem derives
   hypercharge `(-2,3)`.
3. At that pair, the injective standard-key embedding transports the same
   dual identity to the source's normalized SU(5) weights. Actual-source
   Weyl invariance derives `P_Q = P_u = P_e` and `P_d = P_L`.
4. PROFILE-2 supplies nonzero actual radical vectors at all fifteen selected
   weight/charge keys and supported neutral `qque` and `duql` signatures.

`Model.selection_rule_obstruction` therefore excludes universal Abelian
charge prohibition of supported physical delta-B-one signatures. The
continuous-U(1) anomaly cross-check is not used. The flipped Weyl obstruction
and all existing signed/negative-orientation endpoints remain unchanged.

## 5. Lean entry points

### Files

- [PhysicalProfileSource](../../../../../GUT/SU6/SelectionRules/Models/PhysicalProfileSource.lean)
- [ContinuousProfileModel](../../../../../GUT/SU6/SelectionRules/Models/ContinuousProfileModel.lean)
- [AuditContinuousProfileModel](../../../../../GUT/SU6/SelectionRules/Audit/AuditContinuousProfileModel.lean)

The audit is imported by `GUT.lean`. Build it for targeted verification and
then run `lake build`. Local ignored logs are `.lake/build/profile3a-targeted.log`
and `.lake/build/profile3a-full.log`. See the
[verified baseline](../../../../topics/proof-program-context/checkpoints/verified-baseline.md) and
[declaration record](interfaces/finite-charge-profiles.md).

## 6. Scope and limitations

### Realizability And Compatibility

PROFILE-3b is checked: the [SU(5) adapter](../../inputs/GUT/SU5_CHARGE_PROFILES.md) derives
natural profiles from actual character eigenspaces, counts repeated
characters, and preserves field maps and ordered tensors.
PROFILE-3c is checked: the [two-charge SU(6) example](NONUNIFORM_PROFILE_MODEL.md)
constructs actual matter with a nontrivial order-two residual character and
derives its target from traces. Both distinct charges have actual radical
vectors at every SM weight. Its zero-mass radical has dimension 54, so this
is an index-realizability test, not a pure-light-spectrum claim. The separate
nonlinear nonzero-mass regression retains its original role.

PROFILE-1 through PROFILE-3 and MASS-1 through MASS-3 are complete within
the declared scope. No new profile-equality or support premise was added.

## 7. Sources and verification

### Compatibility And Mass Sources

`Model.ofLegacy` embeds every positive-generation legacy continuous Weyl
model and preserves its mass and actual light spectrum exactly.
`ScalarModel` composes the profile target with MASS-3's jointly continuous
equivariant scalar-dependent mass family. Its legacy conversion preserves
the entire converted mass model.

The persistent audit converts the existing nonlinear quadratic benchmark,
retaining a nonzero mass, nonadditivity, a 15-dimensional radical, and the
selection-rule result. It also proves that the incompatible same-total
coefficient profiles from PROFILE-1 cannot be the target of this actual
model class.

These are still torus/residual operator signatures on the general radical,
not new full-SM intertwiners or tensor nonvanishing results. The scalar
interface is the existing unbroken-group interface, not a new full-SU(6)
Higgs sector. Vacuum dynamics, exact SM stabilizers, amplitudes, and
Grassmann/Lorentz nonvanishing are not asserted.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
