# Scalar-dependent model formalization

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../../README.md).

## 1. Result And Status

Declaration map for the established interfaces below. Scalar-dependent families
connect to the scoped SU(6) selection-rule model, with legacy recovery and a
nonlinear benchmark.

### Original Status And Context

Dates, milestone labels and then-pending notes below are checkpoint context,
not a current project-wide status report.

Environment-specific paths were normalized at stage 02; recorded outcomes are unchanged. Commands assume elan, lake and lean on PATH and execution from the repository root.

Status: **LEAN-CHECKED**, MASS-3 (stage 01). See the
[scope dossier](../SCALAR_DEPENDENT_MODEL.md) for hypotheses and boundaries.

## 2. Inputs And Conclusion

The physical model retains its exact infrared dual target and joint coefficient
continuity; residual-action continuity is not added silently.

## 3. Definitions And Conventions

Module paths locate source files; retained `GUT.*` namespaces are compatibility
names, not directory assignments. Duals, signs, coordinate order and action
conventions are those of the named declarations and their displayed formulas;
no convention is changed by this catalogue.

## 4. Proof Structure

Power sources realize nonadditivity; fixed-vacuum evaluation produces the mass
model and preserves legacy mass/spectrum data.

## 5. Lean Entry Points

The catalogue below retains public names, adapters and detailed interface
qualifications. Source declarations, rather than this map, fix elaborated types.

### Generic Realization API

In `Physics.WeylMassFamily`,
[WeylMassPolynomial](../../../../../../Physics/FieldTheory/Yukawa/Mass/WeylMassPolynomial.lean) provides:

- `MultilinearCoupling.powerOfMass`: an actual finite coefficient with
  neutral scalar slots, proved symmetric and equivariant.
- `EquivariantFamily.powerOfMass`, `powerOfMass_apply`, `powerOfMass_zero`,
  `powerOfMass_nonzero`, `quadratic_not_additive`, `continuous_powerOfMass`.
- `EquivariantFamily.Nonadditive`, `quadratic_nonadditive`: an existential
  nonadditivity witness, realized by scalar values (1,1) in the quadratic case.
- `Sector.ofMassAsPower`, `ofMassAsPower_mass`, `ofMassAsPower_zeroVacuum`.

The generic source audit rejects all transitive SU(5)/SU(6) imports.

### Model API

In `GUT.ContinuousWeylFamilyModel.Model`,
[ContinuousWeylFamilyModel](../../../../../../GUT/SU6/SelectionRules/Models/ContinuousWeylFamilyModel.lean)
provides:

- `toMassModel`: the source-derived mass and unchanged infrared data.
- `hyperchargePair_eq_standard`, `proton_functionals_eq_zero`.
- `supportedInvariantOperator`,
  `not_forbidsEverySupportedPhysicalDeltaBOneOperator`.
- `not_forbidsBothOrientations`, `finiteAbelian_not_forbidsBothOrientations`.
- `ofLinearModel`, `ofLinearModel_toMassModel`, `ofLinearModel_mass`,
  `ofLinearModel_lightSpectrum`: no extra continuity input from old models.
- `ofMassAsPower`, `ofMassAsPower_mass`, `ofMassAsPower_toMassModel`.
- `ofMassAsPower_at_one_nonzero`, `ofMassAsPower_quadratic_not_additive`,
  `ofMassAsPower_zeroVacuum`: abstract model lemmas keep the large closed
  benchmark's elaboration separate from the coefficient algebra.

The model includes joint coefficient continuity but not continuity of an
arbitrary residual group action. Its scalar group is `CompactTorus x H`.

## 6. Scope And Limitations

The benchmark uses a neutral residual action; neither faithful finite action nor vacuum dynamics is derived.

## 7. Sources And Verification

The [scope dossier](../SCALAR_DEPENDENT_MODEL.md) supplies related statement and hypothesis context;
internal document links are navigation, not quotations or extra theorem inputs.
Library API references identify proof dependencies, not unproved premises,
except for the explicit literature boundary where stated.

Build counts and warning reports retained below describe their original
checkpoints, not a new build baseline. Commands assume `elan`, `lake` and
`lean` on PATH and execution from the repository root. This formatting pass
changes no Lean source or dependency pin and reruns no Lean build.
See the [documentation topic](../../../../TEMPLATE.md)
for this pass's checks.

### Benchmark and Audit

[WeylMassFamilyBenchmark](../../../../../../GUT/SU6/SelectionRules/Benchmarks/WeylMassFamilyBenchmark.lean)
builds `model H` from `ContinuousWeylFullMass.model H` at degree two. The
checked public results are `toMassModel`, `bare_mass_zero`, `vacuum_one`,
`family_at_one_nonzero`, `family_not_additive`, `mass_nonzero`,
`radical_finrank`, `lightSpectrum`, `supportedInvariantOperator`,
`zeroVacuum_family`, `zeroVacuum_mass`, `zeroVacuum_radical`, and
`exists_nonlinear_sm_radical`.

The persistent
[model audit](../../../../../../GUT/SU6/SelectionRules/Audit/AuditWeylMassFamilyModel.lean)
checks legacy compatibility, a finite `Multiplicative (ZMod 2)` residual
group, actual radical support, joint continuity, and the zero-VEV control.
This example retains the previous neutral residual action, not a newly
constructed faithful finite action.

### Verification

```sh
lake build Physics.FieldTheory.Yukawa.Mass.Audit.AuditMultilinearWeylMass GUT.SU6.SelectionRules.Audit.AuditWeylMassFamilyModel
lake build
```

The two-audit build passed (4177 jobs): 55 axiom-bearing reports, including
23 in the new model audit and five new generic power-source reports.
Full regression passed (4374 jobs, 1328 axiom-bearing reports). Every
printed dependency is among `propext`, `Classical.choice`, and `Quot.sound`;
none uses `sorryAx` or a native-decision axiom. Both audits are imported by
`GUT.lean`. Existing interfaces and dependency pins are unchanged.

The benchmark's nonadditivity is packaged as an existential predicate to
avoid repeated typeclass elaboration over the large closed SU(6) carrier;
the generic proof supplies the actual witness (1,1). All proof sources and
persistent controls are tracked; build/profiling logs under `.lake/build`
are disposable and unnecessary after cloning.
