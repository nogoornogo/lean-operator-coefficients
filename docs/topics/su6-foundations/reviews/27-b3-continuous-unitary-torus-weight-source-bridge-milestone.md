# B3 continuous-unitary torus-weight source bridge milestone

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: B3 continuous-unitary torus-weight source bridge milestone
- Local-model role: none

### Audit result

The following additional stages now kernel-check:

- `Circle^5` maps continuously into the actual determinant-one diagonal
  subgroup of `SU(6)`, covers every diagonal point, and evaluates integral
  characters exactly as normalized ambient Laurent monomials;
- every one-dimensional jointly continuous unitary torus representation has
  a unique integral weight;
- restriction of every finite-dimensional jointly continuous unitary `SU(6)`
  representation decomposes into finitely many such one-dimensional blocks;
- the assembled `Finsupp` Laurent polynomial evaluates to the actual
  restricted trace character by a basis trace calculation;
- this model transfers along a supplied continuous-unitarizable
  representation equivalence and extends to finite virtual combinations,
  whose Laurent polynomial is then Weyl invariant by trace conjugacy.

`GUT/SU6/ProtonStabilityNoGo/Audit/AuditB3.lean` permanently audits the concrete torus, integer weight,
trace realization, transport, and finite-virtual declarations.  Every newly
audited declaration depends only on `propext`, `Classical.choice`, and
`Quot.sound`.  The focused B3 audit completed with 3801 jobs and the full root
build with 3847 jobs.  `git diff --check` passed, and the Lean source tree
contains no `sorry`, `admit`, or declared `axiom`.

This closes the actual-character Laurent source bridge for continuous unitary
representations, but not yet for every intended continuous representation.
The remaining B3 obligation is compact-torus unitarization (or an equivalent
weight-decomposition theorem) from the physical continuity assumptions, plus
the final identification with the exact SM virtual character.  Accordingly,
no final no-go theorem is claimed; A1 and C1 retain their stated source
obligations, C3 remains auxiliary, and D remains independent.

---
