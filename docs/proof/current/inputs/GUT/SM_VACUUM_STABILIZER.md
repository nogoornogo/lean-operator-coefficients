# Stabilizer audit of the constructed VEV

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

### Result

For the existing `StandardSMUVYukawa.vacuum H`, the standard SM image is
**strictly smaller** than the full SU(6) stabilizer. This holds for every
Abelian residual group H in this benchmark, whose residual action is neutral.
Neither the existing mass nor the VEV has been changed.

`StandardSMUVStabilizer.exists_extra_stabilizer` proves the requested
existence statement. `standard_lt_stabilizer` combines the explicit witness
with the previously proved inclusion of the SM image in the stabilizer.
The image, not the covering product itself, is compared with the stabilizer;
the covering group's central kernel does not affect this conclusion.

## 4. Proof structure

### Explicit witness

In human, one-based coordinates, the witness acts by

```text
g(v1,v2,v3,v4,v5,v6) = (-v4,v2,v3,v1,v5,v6).
```

It is `signedTranspositionSU 0 3` in Lean's zero-based `Fin 6` indices.
The existing signed-transposition construction proves unitarity and
determinant one. This mixes a color coordinate and a weak coordinate.
Every element of `StandardSMGroup.hom.range` has matrix entry `(0,3) = 0`,
whereas the witness has entry `-1`; `rotation_not_standard` proves exclusion.
This is an exact symbolic argument, not a numerical sample or a bounded search.

### Why it fixes the same VEV

The proved algebraic coordinates of the analytic UV carrier are
`x = ((w,a),b)`, with `w` in `exteriorPower 2 C^6` and `a,b` in `(C^6)*`.
Writing `e6` for the sixth basis vector, define

```text
c(v wedge u) = u6 * v - v6 * u
P(w,a)      = c(w) + a(e6) * e6
B(x,y)      = b_y(P(w_x,a_x)) + b_x(P(w_y,a_y)).
```

`mass_formula` proves that B is exactly `StandardSMUVMass.mass H`. The
coordinate bridge in `StandardSMUVCoordinates` removes only the casts of
representation equivalences along proved equalities; it introduces no new
mass choice or invariance hypothesis.

The witness fixes both `e6` and the sixth coordinate functional.
`contract_covariant` proves covariance of c by exterior-power extensionality;
`heavyVector_rotation` proves covariance of P. The contragredient action
then gives `mass_rotation` for every pair of actual UV vectors. Finally,
`vacuum_fixed_iff` transfers this to the existing continuous unitary scalar
model, yielding `vacuum_rotation` for the actual VEV.

## 7. Sources and verification

### Scope and audit

`AuditStandardSMUVStabilizer` checks the explicit witness, strict inclusion,
trivial and finite-Abelian neutral examples, and retention of nonzero VEV,
nonzero mass, and exactly 15 SM zero modes. The audited declarations use
only `propext`, `Classical.choice`, and `Quot.sound`.

Consequently this particular scalar/Yukawa completion must not be described
as breaking SU(6) **exactly** to SM. Equality of its stabilizer with SM is
refuted, not merely an unfinished proof. The conditional ordinary-Abelian
selection-rule endpoint and the mass/radical/tensor results are unchanged:
they did not assume that equality or a dynamically selected vacuum.

The full stabilizer is not classified here. Additional symmetry-breaking
scalar data, a scalar potential, vacuum minimization, and decay amplitudes
are not supplied. Any future exact-SM vacuum claim needs a different or
augmented construction, together with a new stabilizer proof.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
