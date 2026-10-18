# E6 Candidate Tangent Lie Algebra

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Updated: stage 01

### Checked Result

**E6-0n is complete.** The actual connected compact candidate's geometric
tangent Lie algebra is Lie-isomorphic over the reals to the existing E6
compact real form, whose complexification was previously identified with
the pinned Geck E6 carrier.

[CompactLieAlgebra](../../../../../Math/LieGroups/E6/Minuscule/CompactLieAlgebra.lean) constructs
`compactTangentRealFormLieEquiv`. Its source is mathlib's `GroupLieAlgebra`
of the actual smooth candidate group, not the model space with an assigned
bracket. The intermediate `compactTangentLieEquiv` has precisely the
previously checked differential identification as its underlying linear map.

## 4. Proof structure

### Proof Route

1. Bundle the actual inclusion into matrix units as the smooth injective
   homomorphism `compactUnits`. Its value is the actual matrix, and its
   inverse value is the actual inverse group element's matrix.
2. Compute its manifold differential in the checked exponential chart.
   Under the standard tangent/model casts it is the same real-form
   inclusion as E6-0m's matrix differential.
3. Apply pinned TauCeti's `lieMap`, its differential formula and
   `unitsLieAlgebraLieEquiv` to obtain a Lie homomorphism to matrices with
   their associative commutator bracket.
4. Prove that its pointwise value is the checked tangent inclusion. The
   existing tangent/model linear equivalence then preserves brackets and
   gives the Lie equivalence to the real form.

The explicit theorem `compact_invariantVectorField_bracket` checks that
`mlieBracket` of the actual left-invariant vector fields, evaluated at one,
maps to `XY - YX`. This guards against accidentally selecting the model
subspace's Lie-ring instance in place of the geometric tangent bracket.
No Lie-compatibility certificate is assumed.

## 6. Scope and limitations

### Remaining Global Gate

The local geometric realization part is now closed: the actual group is
connected and compact, its group operations are smooth, and its geometric
Lie algebra is the intended real form. This still does not distinguish
different global groups with that Lie algebra.

**E6-0o** is a bounded global-form feasibility audit. Check the pinned
classification/integration and central-kernel APIs; identify a concrete
route to the component's exact center and simple connectedness before
starting general foundations. In particular, the full normalizer's
order-27 central scalar has not been assigned to a connected component.
The connected candidate must not yet be named the simply connected compact
E6 group. The existing foundations cost-review gate remains in force.

The actual Spin(10) inclusion, oriented group branching, positive-target
27 model and E6 physical endpoint are still separate open obligations.
No physical hypothesis, conclusion or dependency pin changed.

## 7. Sources and verification

### Verification

[AuditCompactLieAlgebra](../../../../../Math/LieGroups/E6/Audit/AuditCompactLieAlgebra.lean)
checks 11 new declarations against only `propext`, `Classical.choice`,
`Quot.sound`. Concrete examples use the actual units inclusion, Lie
equivalence and explicitly geometric invariant-vector-field bracket.

Targeted: **4031 jobs / 114 reports**, including 103 reused reports.
Full: **5468 jobs / 2370 reports** (2369 lists and one axiom-free report),
standard axioms only. Both new modules are warning-free; ten Python tests
pass. The local geometry modules contain no `sorry`, `admit`, or
`native_decide`.

```sh
lake build Math.LieGroups.E6.Audit.AuditCompactLieAlgebra
lake build
python3 -m unittest discover -s tools/e6 -p 'test_*.py'
```

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
