# Verification

Branch `proof/llhh-kernel-rank`, base `checkpoint 01`, integration target
`proof/sm-rank-enumeration`. No merge or push performed.

Commands:

    lake build Math.RepresentationTheory.ConstantPatternExterior
    lake env lean Physics/StandardModel/Operators/LLHHKernelRank.lean
    lake build Math.RepresentationTheory.Audit.AuditConstantPatternExterior Physics.StandardModel.Operators.Audit.AuditLLHHKernelRank
    lake build
    node tools/layout/check-layout.mjs
    node tools/docs/check-links.mjs
    git diff --check

Focused proofs and audits passed (4140 jobs). Five Math and thirteen Physics
declarations are audited transitively, allowing only `propext`,
`Classical.choice`, `Quot.sound`, with layer dependency checks.
The serialized full build passed (6886 jobs), with no warning/error lines in
`/tmp/llhh-kernel-rank-build.log`. Layout passed for 1543 modules; links passed
for 821 Markdown files, 5048 local links and 94 heading fragments, zero errors.
`git diff --check` passed. No external computation is used as a proof premise.

During development, a tensor additive-instance mismatch was resolved with
the same reducible local instances used by the existing Weinberg interface;
explicit exterior indices were ordered by reindexing the lepton basis to
`Fin 12`. No resource settings, dependencies, pins or audit exceptions changed.
