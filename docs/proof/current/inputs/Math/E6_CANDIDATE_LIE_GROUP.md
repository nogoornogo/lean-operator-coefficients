# E6 Candidate Lie Group

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Updated: stage 01

### Checked Result

**E6-0l is complete.** The actual identity component of the closed SU(27)
normalizer now has a smooth `LieGroup` instance, in addition to its
previously checked compactness and connectedness. Its manifold model is
the actual 78-dimensional real form, with the unchanged subgroup topology.
It is still called the **candidate**, not an identified compact E6 global form.

[CompactLieGroup](../../../../../Math/LieGroups/E6/Minuscule/CompactLieGroup.lean) proves:

- The actual matrix inclusion `compactMatrix` is smooth and injective.
- A continuous map into the candidate is smooth at a point if its matrix
  inclusion is smooth there. The proof uses the constructed local log
  chart, not an assumed embedding or smooth-subgroup certificate.
- Multiplication is smooth by actual matrix multiplication.
- Inversion is smooth because on the actual unitary subgroup it is the
  real-linear continuous star map (conjugate transpose).
- These results instantiate mathlib's `LieGroup` on the checked atlas.

All source conditions are discharged for the actual group operations.
There is no new regularity, center, simple-connectedness or realization
assumption. The previous normalizer/global-exponential negative controls
remain imported by the audit.

## 6. Scope and limitations

### Next Bounded Checkpoint

**[E6-0m](E6_TANGENT_IMAGE.md) is now complete:** the actual differential
is injective with image exactly the real form. Subsequent
[E6-0n](E6_TANGENT_LIE_ALGEBRA.md) implements the units/Lie-functor bridge
and explicitly proves preservation of the geometric tangent bracket.
The next gate concerns the exact center, simple connectedness and global form.

Simple connectedness, exact center, compact E6 global identification,
integrated Spin(10) inclusion, oriented branching and a positive-target 27
model remain open. Retain the cost review before general integration or
global classification foundations. Physical conclusions are unchanged.

## 7. Sources and verification

### Verification

[AuditCompactLieGroup](../../../../../Math/LieGroups/E6/Audit/AuditCompactLieGroup.lean) checks
12 new declarations against the standard allowlist `propext`,
`Classical.choice`, `Quot.sound`; examples instantiate compactness,
connectedness, the Lie-group structure, the smooth matrix inclusion and
both smooth group operations without certificates.

Targeted: **3878 jobs / 92 reports**, including 80 reused reports.
Full: **5449 jobs / 2348 reports** (2347 lists and one axiom-free report),
standard axioms only. Both new modules are warning-free. Ten Python
tooling tests pass.

```sh
lake build Math.LieGroups.E6.Audit.AuditCompactLieGroup
lake build
python3 -m unittest discover -s tools/e6 -p 'test_*.py'
```

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
