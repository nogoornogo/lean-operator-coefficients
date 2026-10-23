# Finite charge-profile declarations

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../../README.md).

## 1. Result And Status

Declaration map for the established interfaces below. Finite profiles recover
resolved targets and, through separate radical/source adapters, actual supported
modes and selection-rule conclusions.

### Original Status And Context

Dates, milestone labels and then-pending notes below are checkpoint context,
not a current project-wide status report.

**LEAN-CHECKED**, PROFILE-1. See the
[scope and argument](../../../inputs/GUT/FINITE_CHARGE_PROFILES.md) for the distinction
between target support and actual radical support.

## 2. Inputs And Conclusion

Profiles have a common positive total. Actual radical support requires the
mass/dual-target hypotheses of the relevant adapter, not just formal
coefficients.

## 3. Definitions And Conventions

Module paths locate source files; retained `GUT.*` namespaces are compatibility
names, not directory assignments. Duals, signs, coordinate order and action
conventions are those of the named declarations and their displayed formulas;
no convention is changed by this catalogue.

## 4. Proof Structure

Faithful coefficient evaluation, dual-index conservation and positive
coefficient bounds feed zero-mode support and source-derived models.

## 5. Lean Entry Points

The catalogue below retains public names, adapters and detailed interface
qualifications. Source declarations, rather than this map, fix elaborated types.

### Modules

| Module | Responsibility |
| --- | --- |
| [FiniteSMTarget](../../../../../../Physics/StandardModel/Spectrum/Representations/FiniteSMTarget.lean) | Extracted fifteen SM weights, old single-charge and singlet targets, and representative-profile identities; namespace `GUT.StandardSMCharacterTarget` retained |
| [FiniteChargeProfiles](../../../../../../Physics/StandardModel/Spectrum/Charges/FiniteChargeProfiles.lean) | Natural distributions, common positive total, integer resolved target, charge-forgetting, pure-target recovery, conditional neutrality |
| [ProfileOperatorSignatures](../../../../../../Physics/StandardModel/Operators/Selection/ProfileOperatorSignatures.lean) | Two supported invariant target signatures at the same charge assignment |
| [AuditFiniteChargeProfiles](../../../../../../Physics/StandardModel/Spectrum/Charges/Audit/AuditFiniteChargeProfiles.lean) | Actual finite residual characters, repeated/distinct charges, negative control, import and axiom audit |

### Core API

In `Physics.FiniteChargeProfiles`:

- `Profiles`, `HasCommonTotal`, `Family`: five natural finite distributions
  and a common positive generation total. No orbit equality is built in.
- `integral_injective`: natural-to-integer coefficient embedding is faithful.
- `targetWithSinglets_apply_smReducedWeight`: coefficient formula at all
  fifteen oriented SM weights, unaffected by singlets.
- `targetWithSinglets_{quark,up,down,lepton,electron}Profile`: recovery of
  the corresponding input distribution.
- `forgetCharges_targetWithSinglets`: common total gives the usual uncharged
  SM target and the summed singlet index.
- `targetWithSinglets_pure`: equality with the existing fixed-charge target.
- `occupied_pure_iff`: the old single-charge case has exactly its specified
  occupied assignment when the total is positive.
- `exists_occupied_compatible`, `exists_occupied_neutral`,
  `exists_occupied_trivial_characters`: conditional occupation and neutrality.
- `exists_supported_signature_pair`: both formal signature classes supported
  by target coefficients, not yet by independently derived radical vectors.

### Actual Radical Extension

The [PROFILE-2 dossier](../PROFILE_ZERO_MODES.md) records the actual-support
bridge and its exclusions. Added modules:

- [SMChiralIndex](../../../../../../Physics/StandardModel/Spectrum/Representations/SMChiralIndex.lean): extracted duality,
  Weyl compatibility, and disjointness of oriented/conjugate SM weights.
- [ProfileChiralIndex](../../../../../../Physics/StandardModel/Spectrum/Charges/ProfileChiralIndex.lean):
  `chiralDifference_target_apply`, `coefficient_lower_bound`,
  `chargesSupported_of_occupied`, and `orbitCompatible_of_dual_target`.
- [ProfileZeroModeSupport](../../../../../../GUT/SU6/SelectionRules/Models/ProfileZeroModeSupport.lean):
  `HasTarget`, `chiral_spectrum`, `profile_le_spectrum`, `exists_zeroMode`,
  `all_occupied_zeroModes`, `exists_actual_signature_pair`, and the
  resulting charge-prohibition obstruction. `legacy_target` and
  `legacy_spectrum` preserve the old interface.

Persistent audits are
[AuditProfileChiralIndex](../../../../../../Physics/StandardModel/Spectrum/Charges/Audit/AuditProfileChiralIndex.lean)
and [AuditProfileZeroModeSupport](../../../../../../GUT/SU6/SelectionRules/Audit/AuditProfileZeroModeSupport.lean).
Build the latter for the targeted audit. Logs are ignored artifacts at
`.lake/build/profile2-targeted.log` and `.lake/build/profile2-full.log`.

### Source-Derived Model

[PhysicalProfileSource](../../../../../../GUT/SU6/SelectionRules/Models/PhysicalProfileSource.lean)
proves `forget_profile`, `hypercharge_of_dual_profile`,
`orbitCompatible_of_dual_profile`, and `source_conclusions` from the actual
mass target. [ContinuousProfileModel](../../../../../../GUT/SU6/SelectionRules/Models/ContinuousProfileModel.lean)
defines `Model` and `ScalarModel`, with derived `profiles_compatible`,
`actual_signature_pair`, and `selection_rule_obstruction`. Positive legacy
mass models preserve mass/spectrum; scalar-family conversion preserves the
entire converted mass model. See [the source dossier](../PROFILE_MODEL.md)
for the completed assembly and acceptance gates.

### Actual SU(5) Adapter

[UnitaryCharacterProfile](../../../../../../Math/RepresentationTheory/Characters/UnitaryCharacterProfile.lean)
proves `internal`, `profile_apply`, `total_profile`, and both directions
between positive multiplicity and a nonzero eigenvector.
[SU5.ChargeProfiles](../../../../../../GUT/SU5/SelectionRules/ChargeProfiles.lean)
derives `kindProfile`, `profiles_totals`, `profiles_compatible`, and `family`
from `OrdinaryAction`. `support_of_occupied` and `supported_profile_tensors`
retain actual field intertwiners and the ordered tensor endpoints.
See [the SU(5) dossier](../../../inputs/GUT/SU5_CHARGE_PROFILES.md) for scope and audit.

### Actual Nonuniform SU(6) Model

[ScalarResidualSource](../../../../../../GUT/SU6/SelectionRules/StandardBranch/ScalarResidualSource.lean)
constructs commuting scalar actions and proves uniform-charge and append
trace formulas for the canonical positive representation.
[NonuniformProfileModel](../../../../../../GUT/SU6/SelectionRules/Benchmarks/NonuniformProfileModel.lean)
proves `fields_dual_character`, `mass_hasTarget`, `nonuniform_not_pure`,
`nonuniform_actual_modes`, and `nonuniform_result`. The target is derived
for any invariant symmetric mass; the concrete inhabitant uses zero mass.
See [the example dossier](../NONUNIFORM_PROFILE_MODEL.md) for the finite
residual specialization, dimensions, and audit commands.

## 6. Scope And Limitations

Formal target occupation is not by itself actual radical support; dual-index
equality is not full-spectrum equality.

## 7. Sources And Verification

The [scope dossier](../../../inputs/GUT/FINITE_CHARGE_PROFILES.md) supplies related statement and hypothesis context;
internal document links are navigation, not quotations or extra theorem inputs.
Library API references identify proof dependencies, not unproved premises,
except for the explicit literature boundary where stated.

Build counts and warning reports retained below describe their original
checkpoints, not a new build baseline. Commands assume `elan`, `lake` and
`lean` on PATH and execution from the repository root. This formatting pass
changes no Lean source or dependency pin and reruns no Lean build.
See the [documentation topic](../../../../TEMPLATE.md)
for this pass's checks.

### Verification

```sh
lake build Physics.StandardModel.Spectrum.Charges.Audit.AuditFiniteChargeProfiles \
  GUT.SU6.Branching.StandardSMCharacterTarget
lake build
```

The targeted build has 3944 jobs and 25 axiom-bearing audit reports.
The full regression result is recorded in
[historical verified baseline](../../../../../topics/proof-program-context/checkpoints/verified-baseline.md).
Logs are local, ignored artifacts at `.lake/build/profile1-targeted.log`
and `.lake/build/profile1-full.log`. Dependency and toolchain pins are unchanged.
