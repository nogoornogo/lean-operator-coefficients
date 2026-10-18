# A1 product-factorization, continuous-factor, and scalar-circle bridges

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: A1 product-factorization, continuous-factor, and scalar-circle bridges
- Local-model role: none

### Audit result

The following additional stages now kernel-check:

- finite-dimensional Burnside density over an algebraically closed field;
- both directions of irreducibility for external tensor products, including
  the multiplicity-space evaluation construction for the converse;
- descent of semisimplicity to the multiplicity representation and its
  resulting irreducibility;
- equivalent ambient-subspace models for both extracted factors, together
  with joint continuity inherited from the original product action;
- direct irreducibility and joint continuity of the defining `SU(3)` triplet,
  complementing the defining `SU(2)` doublet and its center calculation;
- triviality of every continuous circle in the scalar centralizer of an
  irreducible defining restriction.

The remaining general Lie-theory obligation is now represented by the single
structure `ContinuousRepresentationScope.SU2SU3HighestWeightTheory`.  From
this input Lean derives the low-dimensional color list and the weak-center
sign for the continuously extracted factors.  Constructing that structure
for all continuous irreducibles, and collecting the semisimple six-dimensional
restriction into a finite certified block list, remain open.

---
