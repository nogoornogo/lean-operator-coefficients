# C1 coefficient-level physical SM-only spectrum bridge milestone

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: C1 coefficient-level physical SM-only spectrum bridge milestone
- Local-model role: none

### Audit result

`GUT/SU6/ProtonStabilityNoGo/Models/StandardPhysicalSpectrumBridge.lean` now gives the low-energy
spectrum premise a local, auditable form:

- the fifteen explicit non-singlet SM reduced weights are proved pairwise
  distinct and nonzero;
- an exact SM-only coefficient certificate specifies their generation index,
  the arbitrary finite residual-charge spectrum at zero gauge weight, and
  vanishing chiral index at every other nonzero gauge weight;
- this certificate is proved equivalent to equality with the canonical
  charge-resolved `Finsupp`, so no information is silently lost;
- together with the preceding actual source trace theorem it constructs the
  whole product-group character equivalence rather than assuming it;
- arbitrary, continuous, and finite Abelian standard-physical source packages
  then prove the C1 charge equalities and C2 proton-character triviality with
  neither a character-model nor a character-equivalence field and without C3.

The focused C1 audit completed with 3816 jobs and the full root build with
3857 jobs.  Every new audited declaration depends only on `propext`,
`Classical.choice`, and `Quot.sound`.

The remaining universal C1 work is now the existence and reduction of the
homomorphic gauge lift and the extraction of the explicit local chiral-spectrum
and flavor-amplitude hypotheses from every intended physical model.  C3
remains auxiliary, D remains independent, and no final no-go theorem is
claimed.

---
