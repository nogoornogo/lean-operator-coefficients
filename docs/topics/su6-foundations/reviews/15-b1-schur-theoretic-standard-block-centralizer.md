# B1 Schur-theoretic standard-block centralizer

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: B1 Schur-theoretic standard-block centralizer
- Local-model role: none

### Audit result

The following stages now kernel-check:

- an intertwiner between finite-dimensional irreducibles of unequal dimension
  is zero;
- irreducibility is preserved by restriction along a surjective monoid
  homomorphism;
- the concrete `(3,1)`, `(1,2)`, and `(1,1)` product-group blocks are
  irreducible;
- every endomorphism commuting with their `3+2+1` sum is scalar on each block;
- its trace is exactly `3c+2w+s`;
- every traceless commutant element has unique coefficients in the directions
  `Y5=(-2,3,0)` and `X=(1,1,-5)`;
- the resulting traceless commutant is explicitly equivalent to `Complex x
  Complex`;
- conjugation across a representation equivalence preserves both the
  commutant condition and trace.

The reusable `GUT/SU6/ProtonStabilityNoGo/Audit/AuditB1.lean` audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.  The full build completed successfully
with 3784 jobs, and the source tree contains no `sorry`, `admit`, or declared
`axiom`.

The remaining B1 input is geometric/analytic rather than Schur-theoretic:
construct an equivalence between the actual A1 restricted defining
representation and the explicit standard block model, then identify the
anti-Hermitian real form and exponentiated compact torus inside the checked
complexified commutant.

---
