# C1 finite Abelian character-sector source bridge milestone

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: C1 finite Abelian character-sector source bridge milestone
- Local-model role: none

### Audit result

`GUT/SU6/ProtonStabilityNoGo/StandardBranch/FiniteAbelianChargeSectors.lean` now kernel-checks the following
finite-group bridge:

- the residual group `H` is kept distinct from the additive physical charge
  group `Additive (H ->* Circle)`;
- a unitary finite Abelian action commuting with an actual jointly continuous
  unitary `SU(6)` representation decomposes into full simultaneous character
  eigenspaces;
- every such eigenspace is an actual continuous-unitary `SU(6)`
  subrepresentation;
- the distinct active eigenspaces are independent and span the source;
- their direct-sum `SU(6)` representation is equivalent to the original one,
  and therefore has the identical trace character;
- the sectors form an affine charged source for any common central character,
  with finite-charge collisions handled by the existing `Finsupp` model;
- additive neutrality of both proton functionals gives trivial physical
  characters and pointwise phase one on every element of `H`.

The focused `GUT.AuditC1` build completed with 3809 jobs and the full root
build with 3850 jobs.  Every newly audited declaration depends only on
`propext`, `Classical.choice`, and `Quot.sound`.

This closes finite character-sector extraction from a supplied commuting
action, not the universal physical factorization theorem.  It remains to show
that every intended standard-branch residual action, modulo its central gauge
component, supplies precisely such a commuting action, and to establish the
physical low-energy profile and nonzero-amplitude hypotheses.  C3 is not used;
D remains independent; no final no-go theorem is claimed.

---
