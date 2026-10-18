# Self-dual character and mass index

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../../README.md).

## 1. Result And Status

Declaration map for the established interfaces below. Self-dual source
characters yield zero radical dual index and exclude a supplied positive chiral
target in the stated interfaces.

### Original Status And Context

Dates, milestone labels and then-pending notes below are checkpoint context,
not a current project-wide status report.

Updated: stage 01

## 2. Inputs And Conclusion

Source self-duality, an equivariant equivalence or pointwise inverse conjugacy
is supplied as specified by each theorem; invariant symmetric masses are
distinct inputs.

## 3. Definitions And Conventions

Module paths locate source files; retained `GUT.*` namespaces are compatibility
names, not directory assignments. Duals, signs, coordinate order and action
conventions are those of the named declarations and their displayed formulas;
no convention is changed by this catalogue.

## 4. Proof Structure

Character restriction and symmetric-mass index conservation feed faithful target
evaluation and the physical-torus model adapter.

## 5. Lean Entry Points

The catalogue below retains public names, adapters and detailed interface
qualifications. Source declarations, rather than this map, fix elaborated types.

### Declarations

[SelfDualCharacter](../../../../../../Math/RepresentationTheory/Characters/SelfDualCharacter.lean),
namespace `GUT.SelfDualCharacter`:

- `character_eq_inv_of_equiv`
- `restrict_character_eq_dual_of_equiv`
- `restrict_character_eq_dual_of_conjugate_inverse`
- `restrict_character_eq_dual_of_inversion_element`
- `virtualCharacter_restrict_inv`

[SelfDualMassIndex](../../../../../../Physics/FieldTheory/Mass/SelfDualMassIndex.lean), namespace
`GUT.InvariantWeylMass.SymmetricMass`:

- `radical_dual_character_zero_at`: source equality at a tested element
  suffices, without imposing equality on the whole unbroken group.
- `radical_dual_character_zero_of_equiv`
- `restricted_radical_dual_character_zero_of_equiv`
- `restricted_radical_dual_character_zero_of_conjugate_inverse`
- `restricted_radical_dual_character_zero_of_inversion_element`

The source hypothesis is independent of the chosen mass. The restricted
mass need not extend to an ambient-group-invariant mass. These additions
reuse `CharacterRestriction` and `SymmetricMassIndex`; existing APIs are
unchanged. See [the scope](../../../applications/Physics/SELF_DUAL_CHIRALITY.md).

### Verification

[SelfDualChirality](../../../../../../Physics/StandardModel/Spectrum/SelfDualChirality.lean), namespace
`GUT.SelfDualChirality`, adds the DUAL-2 core:

- `forgetCharges_chiralDifference`, `forgotten_target_coefficient`, and
  `forgotten_target_ne_zero`.
- `evaluateGauge_injective` and `evaluated_target_not_zero`.
- `not_has_target_of_zero_source`, `not_has_target_of_source_equiv`, and
  `not_has_target_of_inverse_conjugacy` for an actual invariant mass.

[SelfDualSource](../../../../../../GUT/Common/Chirality/SelfDualSource.lean), namespace
`GUT.StandardChain.SelfDualSource`, connects this to existing model data:

- `gaugeWeight_injective` and `evaluate_forgetCharges` identify the actual
  torus evaluator at residual identity.
- `not_model_of_gauge_character`, `not_model_of_gauge_selfDual`, and
  `not_model_of_inverse_conjugacy` exclude the existing positive model.

The core keeps the legacy pure-weight `Math/LieGroups/SpecialUnitary/RankFive/WeylOrbit` and
`ChargeResolved` dependencies; it does not import actual SU(5) groups or
source representations. The physical-torus adapter is deliberately separate.

## 6. Scope And Limitations

A zero dual index does not reconstruct self-dual modes or determine the full radical.

## 7. Sources And Verification

The [scope dossier](../../../applications/Physics/SELF_DUAL_CHIRALITY.md) supplies related statement and hypothesis context;
internal document links are navigation, not quotations or extra theorem inputs.
Library API references identify proof dependencies, not unproved premises,
except for the explicit literature boundary where stated.

Build counts and warning reports retained below describe their original
checkpoints, not a new build baseline. Commands assume `elan`, `lake` and
`lean` on PATH and execution from the repository root. This formatting pass
changes no Lean source or dependency pin and reruns no Lean build.
See the [documentation topic](../../../../TEMPLATE.md)
for this pass's checks.

### Audits

[AuditSelfDualMassIndex](../../../../../../Physics/FieldTheory/Mass/Audit/AuditSelfDualMassIndex.lean)
checks zero/nonzero masses, nonzero radical at zero index, non-Abelian
pointwise conjugacy, and a U(1) counter-control. It reuses existing scalar
and mass examples from `AuditAbelianMassSpectrum` and is imported by `GUT`.

```sh
lake build Physics.FieldTheory.Mass.Audit.AuditSelfDualMassIndex
lake build GUT.Common.Chirality.Audit.AuditSelfDualSource
lake build
```

DUAL-1 verification: targeted 3676 jobs / 41 axiom reports; full 4440 jobs /
1682 reports. Every reported axiom is one of `propext`, `Classical.choice`,
and `Quot.sound`.

DUAL-2 verification: targeted 3927 jobs / 82 axiom reports; full 4444 jobs /
1703 reports, with the same standard axioms only.
[AuditSelfDualChirality](../../../../../../Physics/StandardModel/Spectrum/Audit/AuditSelfDualChirality.lean)
checks torsion, singlets, vectorlike pairs, zero generations, and a
gauge-versus-residual self-duality counterexample.
[AuditSelfDualSource](../../../../../../GUT/Common/Chirality/Audit/AuditSelfDualSource.lean)
checks the torus bridge and a constructed positive SU(5) source that is
not gauge-self-dual. Both are in the root build. No dependency pins changed;
[SP-1/2](compact-symplectic.md) now supply actual compact symplectic inverse
conjugacy and arbitrary-subgroup applications. Spin(10)/E6 remain pending.
