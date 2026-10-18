# B3 normalized ambient Laurent bridge and theorem-scope audit

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: B3 normalized ambient Laurent bridge and theorem-scope audit
- Local-model role: none

### Audit result

The following additional stages now kernel-check:

- the determinant-one diagonal `SU(6)` character lattice has a canonical
  rank-five integral normal form and an injective map to rational trace-zero
  weights;
- the full `S_6` action is defined on that normal form and is compatible with
  Laurent evaluation on the actual compact diagonal torus;
- multivariable Fourier independence makes the compact-torus Laurent
  evaluator faithful;
- for any supplied actual Laurent realization, trace conjugacy by signed Weyl
  representatives proves full Weyl invariance, and the construction is closed
  under finite integer virtual combinations;
- the resulting character maps to the finite-weight model used in the checked
  fifth-moment classification;
- every continuous character of a finite-dimensional compact torus is a
  unique integer Laurent monomial.

`GUT/SU6/ProtonStabilityNoGo/Audit/AuditB3.lean` permanently audits this layer.  Every audited
declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`.
The full build completed successfully with 3840 jobs, `git diff --check`
passed, and the Lean source tree contains no `sorry`, `admit`, or declared
`axiom`.

This does not close B3: the universal construction of an
`ActualAmbientLaurentModel` from the torus weight decomposition of every
physically admissible continuous/smooth/algebraic finite-dimensional
representation remains open.  The intended final theorem has also been
narrowed from ordinary internal symmetries to ordinary Abelian internal
symmetries.  Its standard-branch route is C1 followed by C2; C3 is recorded
only as a continuous-U(1) anomaly cross-check, while D remains an independent
flipped representation-theoretic obstruction.  No final no-go theorem is
claimed before the A1, B3, and C1 source bridges are closed.

---
