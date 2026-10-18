# Scalar-dependent mass formalization

## 1. Result And Status

Declaration map for the established interfaces below. Equivariant
scalar-dependent families evaluate to invariant symmetric masses, with finite
multilinear sources and linear-Yukawa compatibility.

### Original Status And Context

Dates, milestone labels and then-pending notes below are checkpoint context,
not a current project-wide status report.

Environment-specific paths were normalized at stage 02; recorded outcomes are unchanged. Commands assume elan, lake and lean on PATH and execution from the repository root.

Status: **LEAN-CHECKED**, MASS-1 and MASS-2 (stage 01). The
[proof dossier](../SCALAR_DEPENDENT_MASS.md) fixes the scope. No
polynomial-source classification is claimed. The new physical-model endpoint
is recorded separately in the [MASS-3 dossier](../../../applications/GUT/interfaces/scalar-dependent-model.md).

## 2. Inputs And Conclusion

The separate algebraic, continuous and finite-source APIs retain their own
equivariance, scalar-slot and continuity premises.

## 3. Definitions And Conventions

Module paths locate source files; retained `GUT.*` namespaces are compatibility
names, not directory assignments. Duals, signs, coordinate order and action
conventions are those of the named declarations and their displayed formulas;
no convention is changed by this catalogue.

## 4. Proof Structure

Substitution of covariant slots constructs families; evaluation at a preserved
vacuum and compatibility maps recover the mass interfaces.

## 5. Lean Entry Points

The catalogue below retains public names, adapters and detailed interface
qualifications. Source declarations, rather than this map, fix elaborated types.

### Public API

In `GUT.WeylMassFamily`:

- `EquivariantFamily`: symmetric bilinear coefficients with arbitrary
  equivariant scalar dependence.
- `EquivariantFamily.zero`, `const`, `add`, `restrict`, `atVacuum`.
- `Sector.mass`, `mass_form`, `ofBareMass_mass`, `restrict_mass`.
- `atVacuumOn`, `atVacuumOn_form`, `atVacuumStabilizer`,
  `atVacuumStabilizer_form`.

Finite sources in the same namespace:

- `MultilinearCoupling`: finite complex multilinear coefficients, symmetry,
  and simultaneous scalar-slot/fermion equivariance.
- `MultilinearCoupling.toFamily`, `toFamily_apply`, `toFamily_zero`:
  substitution of covariant real-linear slots and positive-arity vanishing.
- `realCoefficient`, `toFamily_realDiagonal`, `toFamily_real_homogeneous`:
  a real multilinear diagonal and its scaling law for compatible actions.
- `linearSlot`, `conjugateSlot`, `conjugateSlot_apply`.
- `constant`, `constant_toFamily`, `ofLinear`, `ofLinear_toFamily`.
- `EquivariantFamily.sum`, `sum_apply`, `sum_zero`.
- `multilinear_basis_expansion`, `continuous_multilinear_scalar`.
- `MultilinearCoupling.continuous_coefficient`, `continuous_toFamily` and
  `EquivariantFamily.continuous_sum`: scalar-valued coefficient continuity
  and joint continuity in the original scalar and both fermion variables.

In the compatibility namespace `GUT.WeylYukawaMass`:

- `EquivariantYukawa.toFamily` and `Sector.toFamilySector`.
- `Sector.toFamilySector_mass`, `Sector.ofBareMass_toFamilySector`.
- `toFamily_atVacuumOn` and `toFamily_atVacuumStabilizer`.
- `EquivariantYukawa.toMultilinearCoupling`, `toMultilinearCoupling_toFamily`
  and `toMultilinearCoupling_atVacuumOn`: actual degree-one source recovery.

The extracted `SymmetricMass`, `InvariantVacuum`, zero constructors, and
vacuum stabilizer retain their old namespaces. `SymmetricMass.ext` and
`restrict`, and `InvariantVacuum.restrict`, are additional generic helpers.
The generic core and audit import no SU(5)/SU(6) module; the compatibility
adapter intentionally imports the legacy linear interface and its closure.

## 6. Scope And Limitations

No classification of every scalar-dependent source or dynamical vacuum selection is asserted.

## 7. Sources And Verification

The [scope dossier](../SCALAR_DEPENDENT_MASS.md) supplies related statement and hypothesis context;
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
lake build Physics.FieldTheory.Yukawa.Audit.AuditWeylMassFamily Physics.FieldTheory.Yukawa.Audit.AuditMultilinearWeylMass Physics.FieldTheory.Yukawa.Audit.AuditWeylMassFamilyCompatibility
lake build
```

At MASS-2 the combined three-audit targeted build passed (3844 jobs). Its 51 printed
axiom-bearing declarations use only `propext`, `Classical.choice`, and
`Quot.sound`; none uses `sorryAx` or a native-decision axiom. The finite-source
audit adds 27 reports and the compatibility audit adds two. All three
persistent audits are imported by `GUT.lean`.
That milestone's full regression passed (4370 jobs, 1300 standard-axiom reports), including
the old SU(5)/SU(6) endpoints.
The latest full regression result is recorded in the
[verified baseline](../../../../../topics/proof-program-context/checkpoints/verified-baseline.md).
Dependency pins and toolchain are unchanged.
