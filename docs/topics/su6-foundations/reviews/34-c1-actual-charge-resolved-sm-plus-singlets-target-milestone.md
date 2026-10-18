# C1 actual charge-resolved SM-plus-singlets target milestone

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: C1 actual charge-resolved SM-plus-singlets target milestone
- Local-model role: none

### Audit result

`GUT/SU6/Branching/StandardSMCharacterTarget.lean` now kernel-checks the
representation-theoretic target side of the physical C1 bridge:

- normalized `SU(5)` weights embed injectively into the standard physical
  compact four-torus, and the explicit fifteen weights agree with the B3 SM
  exponents;
- pairing those weights with characters of an arbitrary Abelian residual
  group gives a faithful evaluator by Dedekind linear independence, including
  for finite Abelian groups;
- every finite charge-resolved character is realized by an actual finite
  virtual sum of one-dimensional product-group representations;
- the exact SM target permits arbitrary finite virtual gauge singlets with
  arbitrary residual characters, and their zero gauge weight is proved not to
  alter the five SM charge profiles;
- whole-character equivalence with that actual target recovers the exact C1
  spectrum, `k_Q = k_u = k_e`, `k_d = k_L`, and triviality of both proton
  characters through C1 followed by C2, with explicit finite-Abelian and
  standard-central specializations.

All computational equalities use kernel reduction rather than
`native_decide`.  `GUT/SU6/ProtonStabilityNoGo/Audit/AuditC1.lean` permanently audits the new bridge;
every new declaration depends only on `propext`, `Classical.choice`, and
`Quot.sound`.  The focused C1 audit completed with 3814 jobs and the full root
build with 3855 jobs.  `git diff --check` passed, and the audited source
contains no `sorry`, `admit`, declared `axiom`, or native-decision axiom.

This is not the final C1 source theorem.  The remaining physical bridge must
derive the supplied gauge lift and whole-character equivalence from the
low-energy SM-only spectrum and flavor assumptions.  C3 remains only an
auxiliary continuous-`U(1)` anomaly cross-check, D remains independent, and no
final no-go theorem is claimed before A1, B3, and C1 are closed.

---
