# actual A1-to-B1 complexified commutant transport

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: actual A1-to-B1 complexified commutant transport
- Local-model role: none

### Audit result

The following additional stages now kernel-check:

- each weak-doublet constituent label selects a canonical index, and the
  color, weak, and singlet indices are pairwise distinct and exhaustive;
- evaluation at those indices is a linear equivalence from the dependent
  direct sum to the ordered product of the actual constituent spaces, with an
  explicit inverse assembled from three `DFinsupp.single` terms;
- this equivalence intertwines the group actions and composes with the A1
  semisimple-decomposition equivalence;
- Schur's lemma applies to the actual blocks of dimensions `3`, `2`, and `1`;
- the actual block-scalar trace is `3c+2w+s`, and every traceless commutant
  endomorphism has a unique pair of complex `Y5/X` coefficients after
  transport;
- the result is composed with the physical injective-embedding and commuting
  nontrivial hypercharge-circle hypotheses.

`GUT/SU6/ProtonStabilityNoGo/Audit/AuditA1.lean` and `GUT/SU6/ProtonStabilityNoGo/Audit/AuditB1.lean` report only `propext`,
`Classical.choice`, and `Quot.sound` for the new declarations.  The full build
completed successfully with 3785 jobs, with no `sorry`, `admit`, or declared
`axiom` in the project sources.

The remaining B1 step is genuinely group-geometric: identify the
anti-Hermitian real form of this checked complex commutant and prove the
exponentiation and integral-lattice description of the compact centralizer
torus.

---
