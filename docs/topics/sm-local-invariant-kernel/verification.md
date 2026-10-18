# Verification

## Contract — stage 01

- Initial state: clean `proof/sm-ql-support-classification`.
- Bounded child: `proof/sm-local-invariant-kernel`, targeting its unmerged
  parent under the recorded child-branch exception.
- Plan frozen before implementation. No new proof result claimed yet.
- Checks and endpoint status will be recorded after formalization.

## Proof checkpoint and stop

- Generic finite matrix/kernel equivalence, rank criterion, generator
  exhaustiveness and polynomial sampling/grid proofs implemented.
- Actual SL(2,C) generation is discharged from the pinned transvection
  theorem. The one-left-Weyl finite-kernel control is unconditional.
- Focused source builds passed after correcting matrix-coordinate rewriting,
  polynomial evaluation transport and explicit kernel/basis instances.
  No pins, heartbeats, custom axioms, sorry or audit exceptions changed.
- `lake build Math.RepresentationTheory.Audit.AuditLocalInvariantKernel
  Physics.FieldTheory.Spinor.Audit.AuditWeylKernelTests`: passed; Math layer
  check and 13 Math / 8 Physics strict transitive axiom checks passed.
  Final focused builds emitted no warnings.
- Serialized full `lake build`: passed, 6861 jobs; disposable output in
  `/tmp/sm-local-invariant-kernel-full-build.log`, outside source control.
- `node tools/layout/check-layout.mjs`: passed; 1518 modules, layers,
  imports, cycles, aggregate coverage and relocation audits OK.
- `node tools/docs/check-links.mjs` and `git diff --check`: passed, repeated
  after final result/status/navigation edits. Staged diff checked before
  commit.
- The actual SM connection reaches the planned special-unitary generating
  family gate. No missing source/action/generation premise is claimed proved.
- No parent/master integration or remote push performed.

The verified checkpoint is the commit containing this record, with its hash
reported after creation. The actual fixed-input endpoint remains open at
the planned SU(3) generating-family stop; no generic conditional premise is
reported as a proved SM discharge.
