# E6 Candidate Scalar Center

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Updated: stage 01

## 4. Proof structure

### Checked Upper Bound

**E6-0p is complete.** For the actual connected compact matrix candidate
`H = compactIdentityComponent`, its center is a finite cyclic group whose
order divides 27. This is an upper bound, not an identification of the
center with all 27th roots or with the cube roots.

[CompactCenter](../../../../../Math/LieGroups/E6/Minuscule/CompactCenter.lean) proves:

- `compact_center_commutes_real`: a central group element commutes with
  every actual real-form matrix, by uniqueness of derivatives of
  `g * exp X = exp X * g` at zero.
- `compact_commutant_scalar`: real/imaginary decomposition extends this
  commutation to the complex E6 algebra; the existing scalar commutant
  theorem then applies.
- `compact_mem_center_iff_scalar`: an element already in `H` is central
  exactly when its actual matrix is scalar.
- `compactCenterRoot`: an injective group homomorphism from `Z(H)` to the
  complex 27th roots of unity, using the SU(27) determinant equation.
- `compactCenter_finite`, `compactCenter_isCyclic`,
  `compactCenter_card_dvd`, `compact_center_pow`: finiteness, cyclicity,
  center order dividing 27 and every central element's 27th power equal
  to one, without a supplied center certificate.

## 6. Scope and limitations

### Remaining Boundary

After the actual-model milestone, the separately
scoped [order-three construction](E6_CENTER_THREE.md) proves that its ninth
power lies in `H`, using Cartan grading weights `1, -2, 4`. The center now
satisfies `3 divides |Z(H)| divides 27`; these bounds do not prove its exact
order. The actual 27 does not descend to the center quotient. The later
[cubic package](E6_CUBIC_CENTER.md) proves group invariance of a nonzero
cubic and thereby sharpens these bounds to an exact order-three center.
It also proves the full normalizer's order-27 scalar lies outside `H`.
These later proofs do not reopen the E6-0 feasibility audit or complete the global form.

Simple connectedness, global compact E6 identification and
actual Spin inclusion remain distinct open obligations. Follow the
[global-form audit and cost gate](../../../../topics/e6-global-topology/decisions/E6_GLOBAL_FORM_AUDIT.md) before general
integration/classification work. No physical endpoint or assumption changed.

## 7. Sources and verification

### Verification

[AuditCompactCenter](../../../../../Math/LieGroups/E6/Audit/AuditCompactCenter.lean) checks all
14 new declarations against `propext`, `Classical.choice`, `Quot.sound`.
Examples use the actual center, and retain the full normalizer's negative
order-three-exponent control without inferring component membership.

Targeted: **4035 jobs / 128 reports** (114 reused).
Full: **5470 jobs / 2384 reports** (2383 lists, one axiom-free), standard
axioms only. Both new modules are warning-free and contain no `sorry`,
`admit` or `native_decide`. Ten tooling tests pass.

```sh
lake build Math.LieGroups.E6.Audit.AuditCompactCenter
lake build
python3 -m unittest discover -s tools/e6 -p 'test_*.py'
```

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
