# E6 Local Exponential Chart

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Updated: stage 01

### Checked Result

**E6-0j is complete.** `compactExpChart` is an actual
`OpenPartialHomeomorph compactMatrixLieAlgebra compactIdentityComponent`.
Its source contains zero and its target contains one. Both are proved
open in the existing subspace topologies. The model has real dimension 78.

The forward map is the actual matrix exponential. On the entire target,
the inverse, coerced to matrices, is `logOneAdd` applied to `g - 1`.
Both inverse laws and continuity on the chart domains are kernel-checked.
The ambient logarithm is analytic at every target matrix minus one.
No chart-existence, radius, or group-realization certificate is an input.

## 4. Proof structure

### Construction

- [LocalInverseChart](../../../../../Math/Topology/LocalInverseChart.lean) shrinks
  neighborhoods of two locally inverse continuous maps to matching open
  sets. It can retain prescribed neighborhood bounds.
- [CompactChart](../../../../../Math/LieGroups/E6/Minuscule/CompactChart.lean) bundles the
  E6-0h exponential into the actual identity component. The ambient
  exponential is continuous in its real-form argument.
- A finite-dimensional linear retraction totalizes the logarithm as a
  real-form-valued function. It is the identity on the real form. E6-0i's
  local logarithm membership proves that it changes nothing near one,
  and the chart target is explicitly constrained to that equality locus.
  No projected logarithm is passed off as an ambient logarithm outside
  the proved target.
- TauCeti's local inverse equations and analytic logarithm, together with
  the checked real-form membership, supply all chart hypotheses.

The construction uses classical choices of complements and neighborhoods;
it does not provide numerical radii. Neither global injectivity nor global
surjectivity of the exponential is asserted. The previous periodic scalar
negative control remains in the audit.

## 6. Scope and limitations

### Next Bounded Checkpoint

The pinned mathlib has `Homeomorph.mulLeft`, open partial homeomorphism
composition, and `ChartedSpace`. These allow translation of the checked
identity chart to all points without a general closed-subgroup theorem.
**[E6-0k](E6_SMOOTH_ATLAS.md) is now complete:** translated charts, analytic
transitions and a smooth manifold instance are checked. Subsequent work
through [E6-0n](E6_TANGENT_LIE_ALGEBRA.md) also proves smooth group operations
and the geometric tangent Lie comparison. Global form remains separate.

The subgroup is still a **connected compact candidate**, not yet an
identified compact E6 global form. Simple connectedness, exact center,
integrated Spin(10) inclusion, oriented branching and a positive-target
27 model remain open. Keep the cost review before general integration or
manifold foundations. No dependency or physical-assumption changes.

## 7. Sources and verification

### Verification

[AuditCompactChart](../../../../../Math/LieGroups/E6/Audit/AuditCompactChart.lean) checks
19 new declarations against `propext`, `Classical.choice`, and `Quot.sound`.
It instantiates both chart inverse laws, open domains, dimension 78,
the actual matrix-log identity, and the earlier global-converse negative
control. All three new modules are warning-free.

Targeted: **3851 jobs / 66 reports**, including 47 reused reports.
Full: **5445 jobs / 2322 reports** (2321 lists and one axiom-free report),
all standard axioms only. Ten Python tooling tests pass.

```sh
lake build Math.LieGroups.E6.Audit.AuditCompactChart
lake build
python3 -m unittest discover -s tools/e6 -p 'test_*.py'
```

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
