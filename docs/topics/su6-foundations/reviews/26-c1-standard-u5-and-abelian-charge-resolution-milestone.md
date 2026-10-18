# C1 standard U(5) and Abelian charge-resolution milestone

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: C1 standard `U(5)` and Abelian charge-resolution milestone
- Local-model role: none

### Audit result

The following additional stages now kernel-check:

- the standard block map `U(5) -> SU(6)` is an injective group homomorphism
  and contains the full determinant-one diagonal torus;
- restriction of actual and finite virtual trace characters agrees on that
  lifted torus, and any supplied ambient Laurent model evaluates the same
  restricted character;
- the rank-five integer exponent is canonically separated into a rank-four
  normalized `SU(5)` weight and an Abelian charge obtained from total degree;
- push-forward to a finite charge group sums all colliding integer lifts;
- full `S_5` invariance survives this push-forward and forces equality of the
  complete charge profiles of `Q,u^c,e^c` and of `d^c,L`;
- both standard proton functionals vanish for exact pure-SM profiles and for
  suitably selected occupied sectors of family-dependent profiles;
- these conclusions specialize to arbitrary finite Abelian groups and to
  `ZMod N`, and use no continuous-anomaly equation.

`GUT/SU6/ProtonStabilityNoGo/Audit/AuditC1.lean` permanently audits these declarations.  Every audited
declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`.
The focused audit build completed successfully with 3801 jobs, and the full
root build completed with 3843 jobs.

This milestone is conditional and does not close C1 or the final no-go.  The
universal B3 Laurent provider, the factorization of every physically intended
standard residual Abelian action through the integer central degree, and the
physical low-energy spectrum interpretation remain explicit obligations.
C3 remains only a continuous-`U(1)` anomaly cross-check, and the flipped D
obstruction remains logically independent.

---
