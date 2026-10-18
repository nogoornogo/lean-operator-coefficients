# concrete standard sl2(Complex) realization for the A1 highest-weight bridge

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: concrete standard `sl2(Complex)` realization for the A1 highest-weight bridge
- Local-model role: none

### Audit result

The following additional stages now kernel-check:

- the standard trace-zero two-by-two matrices `H`, `E`, and `F` satisfy the
  `sl2` commutator relations;
- these three matrices span the complete Lie algebra `sl2(Complex)`;
- every one-dimensional complex module over this concrete Lie algebra has
  zero action;
- the resulting `SU2StandardLieModel` supplies the abstract lowering-string
  model and hence the checked `SU(2)` highest-weight dimension certificate.

The remaining `SU(2)` bridge is now representation-dependent: differentiate
each intended continuous group representation into this standard Lie algebra,
prove the differentiated action irreducible, identify the action of the
nontrivial center element by integration, and show that zero differential
implies trivial group action.  The independent `SU(3)` highest-weight theorem
also remains open.

`GUT/SU6/ProtonStabilityNoGo/Audit/AuditA1.lean` now permanently audits the standard triple, its spanning
theorem, the one-dimensional action theorem, and the resulting highest-weight
certificate.  Every audited declaration reports only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx` or project axiom.  The
full build completed successfully with 3782 jobs.

---
