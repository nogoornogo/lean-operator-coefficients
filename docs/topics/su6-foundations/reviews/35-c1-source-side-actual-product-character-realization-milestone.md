# C1 source-side actual product-character realization milestone

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: C1 source-side actual product-character realization milestone
- Local-model role: none

### Audit result

`GUT/SU6/ProtonStabilityNoGo/StandardBranch/StandardPhysicalCharacterBridge.lean` now kernel-checks the actual
source side of the charge-resolved C1 bridge:

- at the standard hypercharge pair `(-2,3)`, normalization of an ambient
  weight is proved to retain exactly its physical-torus exponent while its
  total degree supplies the standard-central residual charge;
- the physical torus, standard-central gauge lift, and independent residual
  sector character define an actual product-group representation on every
  original charged sector vector space;
- its trace is exactly the faithful charge-resolved evaluator, and finite
  virtual assembly gives the source's canonical resolved character;
- on each full residual-character sector, the reconstructed residual action
  agrees in the original source space with the supplied gauge-twisted physical
  action;
- consequently the source-side `IsCharacterModel` certificate is derived, and
  actual SM-plus-singlets target-character equivalence yields the exact C1
  charge equalities and C2 proton-character conclusion for arbitrary,
  continuous, and finite Abelian residual groups without a C3 premise.

`GUT/SU6/ProtonStabilityNoGo/Audit/AuditC1.lean` permanently audits this chain.  The focused audit
completed with 3815 jobs and every newly audited declaration depends only on
`propext`, `Classical.choice`, and `Quot.sound`.  The full root build completed
with 3856 jobs.  The audited source contains no `sorry`, `admit`, declared
`axiom`, or `native_decide` use.

This does not yet derive the standard-central homomorphic gauge lift for every
physical model or derive target-character equivalence from a precise SM-only
low-energy spectrum and flavor hypothesis.  Those interpretation inputs remain
explicit; C3 is auxiliary, D is independent, and no final no-go theorem is
claimed.

---
