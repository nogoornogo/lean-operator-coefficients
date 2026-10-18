# topological two-torus structure of the actual B1 centralizer

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: topological two-torus structure of the actual B1 centralizer
- Local-model role: none

### Audit result

The following additional stages now kernel-check:

- coefficient reconstruction from the determinant-one circle triples into the
  actual `SU(6)` matrix centralizer is continuous, proved entrywise using
  continuous scalar multiplication and finite-dimensional coordinate maps;
- reconstruction preserves one and multiplication and recovers the three
  block coefficients exactly;
- the compact coefficient group and the actual physical centralizer are
  continuously group-equivalent, with inverse continuity obtained from the
  compact-to-Hausdorff inverse theorem;
- composing with the explicit coefficient-level parameterization proves that
  the actual physical centralizer is continuously group-equivalent to
  `Circle x Circle`.

`GUT/SU6/ProtonStabilityNoGo/Audit/AuditB1.lean` permanently audits continuity of reconstruction and the
final `ContinuousMulEquiv`.  Both declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`.  The full build completed successfully
with 3791 jobs, and the Lean source tree contains no `sorry`, `admit`, or
declared `axiom`.

The next B1 stage is to classify continuous circle homomorphisms into this
checked two-torus by their integer exponent pair, then connect that integral
lattice to the checked anti-Hermitian `Y5/X` real form.

---
