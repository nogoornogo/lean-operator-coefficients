# retention and ordering data for the actual A1 weak-doublet decomposition

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: retention and ordering data for the actual A1 weak-doublet decomposition
- Local-model role: none

### Audit result

The following additional stages now kernel-check:

- the group-algebra semisimple decomposition is a `Representation.Equiv` from
  the original representation to the dependent direct sum of its actual
  simple blocks;
- weak-doublet branch counts force the complete block list to be a permutation
  of `[color3, weak2, singlet]`;
- the actual classified decomposition therefore has exactly three blocks,
  its semantic-label map is injective, and each standard label occurs at a
  unique constituent index;
- the physical injective-embedding theorem now returns this classified
  decomposition without discarding the actual constituent spaces; the older
  branch-count theorem is retained as a projection.

`GUT/SU6/ProtonStabilityNoGo/Audit/AuditA1.lean` audits these new bridges and reports only `propext`,
`Classical.choice`, and `Quot.sound`.  The full build completed successfully
with 3784 jobs.  The source tree contains no `sorry`, `admit`, or declared
`axiom`.

The next algebraic step is to use the three unique constituent indices to
reindex the dependent direct sum as an ordered `3+2+1` product and feed that
equivalence to the generic B1 Schur theorem.

---
