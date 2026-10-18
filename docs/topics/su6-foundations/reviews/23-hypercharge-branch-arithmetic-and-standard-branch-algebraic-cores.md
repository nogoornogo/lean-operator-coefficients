# hypercharge branch arithmetic and standard-branch algebraic cores

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: hypercharge branch arithmetic and standard-branch algebraic cores
- Local-model role: none

### Audit result

The following additional stages now kernel-check:

- every primitive centralizer cocharacter with neutral weak block is the
  flipped pair up to sign, while neutral singlet block gives the standard pair
  up to sign;
- an injective actual physical-centralizer circle therefore has the flipped or
  standard pair under the explicit oriented weak-or-singlet neutrality
  hypothesis;
- primitive neutral-block arithmetic by itself has a third color-neutral pair
  `(0,1)` up to sign, so the exact SM-only representation-theory bridge cannot
  be replaced by this weaker assumption;
- in the normalized `Fin 5` Laurent model, full `S_5` Weyl invariance equates
  the three standard `10` representative coefficients and the two
  anti-fundamental representative coefficients at every residual shift;
- explicit `SU(5)` orbit charge equalities neutralize both proton-decay
  functionals in any additive commutative charge group;
- for one rational, and hence family-universal, charge assignment, the two
  proton functionals equal the stated combinations of the three mixed-anomaly
  coefficients and vanish when those coefficients vanish.

`GUT/SU6/ProtonStabilityNoGo/Audit/AuditHyperchargeStandard.lean` permanently audits these declarations.
It reports only `propext`, `Classical.choice`, and `Quot.sound`.  The full build
completed successfully with 3817 jobs, `git diff --check` passed, and the Lean
source tree contains no `sorry`, `admit`, or declared `axiom`.

The remaining B3 step is to derive oriented weak-or-singlet neutrality and
exclude the color-neutral possibility from the exact SM-only virtual
representation hypothesis.  For C1, the remaining bridge realizes the
physical charge-resolved restriction in the normalized Weyl-invariant model
and identifies its coefficients with chiral multiplicities.  The checked C3
identity does not promote globally cancelled family-dependent anomalies to
family-by-family vanishing.

---
