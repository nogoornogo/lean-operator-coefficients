# C1 arbitrary block-centralizer gauge-lift milestone

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: C1 arbitrary block-centralizer gauge-lift milestone
- Local-model role: none

### Audit result

`GUT/SU6/ProtonStabilityNoGo/StandardBranch/StandardBlockGaugeCancellation.lean` now avoids the unjustified
standard-central reduction for finite Abelian residual groups:

- the two proton charge functionals are invariant under arbitrary color/weak
  block-gauge shifts in every additive Abelian group;
- the checked actual compact centralizer supplies these block characters
  directly, so no fifth root of a finite-group character is assumed;
- finite physical sources with gauge-twisted actions sharing one lift are
  decomposed into their actual gauge-removed character sectors, with an exact
  representation equivalence back to each source and a proof that restoring
  the common lift recovers the physical action;
- coefficient-level SM-only data on this external finite-weight character
  imply the C1 orbit equalities, and block cancellation then gives trivial
  physical proton characters through C2 for arbitrary and finite Abelian
  residual groups.

The focused C1 audit and the full root build succeed; the latter completed
with 3858 jobs.  Every newly audited declaration depends only on `propext`,
`Classical.choice`, and `Quot.sound`, and the changed source contains no
`sorry`, `admit`, declared `axiom`, or `native_decide` use.

This remains a conditional source theorem: universal existence of the common
homomorphic lift, centralization of the surviving semisimple subgroup, and the
identification of the five observed field characters with the block-twist
formula are explicit certificates.  C3 remains auxiliary, D remains
independent, and no final no-go theorem is claimed.
