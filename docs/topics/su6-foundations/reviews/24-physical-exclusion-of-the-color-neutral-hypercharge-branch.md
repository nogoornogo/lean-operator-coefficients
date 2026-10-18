# physical exclusion of the color-neutral hypercharge branch

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: physical exclusion of the color-neutral hypercharge branch
- Local-model role: none

### Audit result

The following additional stages now kernel-check:

- signed representatives in `SU(6)` implement arbitrary transpositions of
  distinct diagonal coordinates by conjugation;
- the color-neutral diagonal subtorus has a faithful normalized `Finsupp`
  Laurent evaluator, and its algebraic `(5 6)` action agrees with the actual
  signed Weyl conjugation;
- every finite virtual `SU(6)` restricted trace character is fixed by that
  action, while the explicit normalized SM chiral target is not;
- this obstruction persists for every nonzero integer generation count after
  adding any integer virtual multiplicity of gauge singlets;
- the concrete block map `SU(3) x U(2) -> SU(6)` is an injective group
  homomorphism and contains every point of the color-neutral diagonal torus;
- the five SM multiplets are realized as actual finite-dimensional
  representations of `SU(3) x U(2)`, and the trace character of their finite
  virtual chiral target is exactly the normalized Laurent target on that
  torus;
- consequently the actual one-generation physical target is not character
  equivalent to the restriction of any finite virtual `SU(6)`
  representation;
- primitive cocharacter arithmetic now reduces B3 to standard or flipped
  from an oriented neutral block once this color-neutral pair is excluded.

`GUT/SU6/ProtonStabilityNoGo/Audit/AuditHyperchargeStandard.lean` permanently audits the generic Weyl
representative, faithful evaluator, source invariance, concrete physical
embedding, target-character equality, no-uplift theorem, and sharpened
arithmetic reduction.  Every audited declaration depends only on `propext`,
`Classical.choice`, and `Quot.sound`.

The full build completed successfully with 3821 jobs.  Direct audit execution
and `git diff --check` passed, and the Lean source tree contains no `sorry`,
`admit`, or declared `axiom`.  The remaining B3 obligation is to derive the
oriented neutral defining block, with its conjugacy and orientation transport,
from the exact SM-only virtual representation-ring hypothesis; color
neutrality itself is no longer an open branch.

---
