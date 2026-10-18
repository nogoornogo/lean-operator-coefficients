# anti-Hermitian real form of the actual B1 commutant

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: anti-Hermitian real form of the actual B1 commutant
- Local-model role: none

### Audit result

The following additional stages now kernel-check:

- a skew-adjoint finite-dimensional complex operator can have an eigenvalue
  on a nonzero eigenvector only when that eigenvalue is purely imaginary;
- applying this fact to the actual color and weak constituent ranges forces
  both complex `Y5/X` coefficients of every skew-adjoint trace-zero commutant
  element to be `i` times unique real coefficients;
- the converse is proved on the original Euclidean representation, without
  treating the arbitrary decomposition equivalence as an isometry: pairwise
  constituent orthogonality makes every real `i*(a*Y5+b*X)` combination
  skew-adjoint, and the block trace computation makes it traceless;
- the resulting `SkewTracelessCommutant` is explicitly equivalent to
  `Real x Real`.

`GUT/SU6/ProtonStabilityNoGo/Audit/AuditB1.lean` now audits the eigenvalue lemma, both directions of the
real-form theorem, and the final equivalence.  They depend only on `propext`,
`Classical.choice`, and `Quot.sound`.  The full build completed successfully
with 3790 jobs, and the Lean source tree contains no `sorry`, `admit`, or
declared `axiom`.

What remains at this interface is topological and differential: upgrade the
actual-centralizer group equivalence to a continuous equivalence, relate its
tangent map to this checked real form, and classify the integral lattice of
circle homomorphisms.

---
