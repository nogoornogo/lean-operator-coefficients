# C5 Master Integration

The user accepted the fixed-scope endpoint, closed further extensions and
explicitly requested the merge. The historical working branch was
`proof/weyl-higgs-current-completeness`; the integration target is `master`.
The topic was merged with `git merge --no-ff`, without conflicts. Master
had not advanced beyond the topic's base, and the merged proof, aggregate
and diagnostic sources are identical to the accepted topic versions.
Git ancestry records the merge and both parents.

## Merged-state verification

Before integration, the focused native-consumer/audit build passed 4030 jobs.
On master, the same focused build passed 4030 jobs, all six strict inventories
were freshly elaborated and the serialized full build passed **8004 jobs**.
The inventories check **1143 declarations transitively**, with only propext,
Classical.choice and Quot.sound allowed. Import-layer and nonempty-inventory
gates are unchanged. The [verification record](verification.md) gives the
namespace counts and reproducible resource wrapper.

Checks retain cores 0,1, two compiler threads, a 16 GiB address-space guard,
default elaboration/kernel/recursion limits and 180/540-second focused/full
ceilings. No builds were run concurrently. The full build replays existing
module-system import advisories and unrelated deprecation/linter warnings;
the accepted C5 sources introduce no tactic/linter warning.

Using the bounded wrapper from the verification record, the merged-state
commands were:

```sh
bounded 180 lake build Physics.FieldTheory.Jets.WeylHiggsCompleteLiterature Physics.FieldTheory.Jets.Audit.AuditWeylHiggsFirstCompletion
bounded 180 lake env lean -j2 Math/Algebra/Audit/AuditMixedScalarInclusion.lean
bounded 180 lake env lean -j2 Physics/FieldTheory/Jets/Audit/AuditWeylHiggsCurrent.lean
bounded 180 lake env lean -j2 Math/Algebra/Audit/AuditMixedFirstWaves.lean
bounded 180 lake env lean -j2 Physics/FieldTheory/Jets/Audit/AuditWeylHiggsWaves.lean
bounded 180 lake env lean -j2 Math/Algebra/Audit/AuditMixedFirstTensor.lean
bounded 180 lake env lean -j2 Physics/FieldTheory/Jets/Audit/AuditWeylHiggsFirstCompletion.lean
bounded 540 lake build
python3 tools/derivative-literature/check-weyl-higgs-finite.py
python3 tools/derivative-literature/check-weyl-higgs-literature.py
node tools/layout/check-layout.mjs
python3 tools/docs/check-topic-index.py
python3 tools/docs/check-work-metadata.py
node tools/docs/check-links.mjs
git diff --check
```

Both exact diagnostics pass. The native queue processes Li, Murphy and DHM,
including sign/factor controls and continuation after a deliberately altered
Li factor. The finite matrix and omission tests remain diagnostics rather
than theorem premises. Layout passes for 2508 modules; topic navigation,
portable metadata, local links and diff checks pass on the final integration
documents. Those recording edits are documentation only; no further Lean
build was rerun for them.

## Literature, scope and cleanup

The topic's [source register](references.md) was reconciled with
[RELATED_LITERATURE](../../proof/RELATED_LITERATURE.md) before integration.
The pinned Li/Murphy entries describe complete native coordinates in the
fixed free one-flavor sector; DHM retains its independent convention role.
Their inspection limits, result links and derivative/Li coverage agree with
the [completed theorem](results.md). No new literature premise is introduced.

The result fixes the whole mixed grade (2,4,1), actual global covering-SM
and SL(2,C) actions, all free equations and linear IBP. It preserves the
published input interfaces, dependency pins and root README. Multi-flavor,
Hermitian real-form and interacting-model extensions remain separate work;
there is no remaining contracted formalization or validation obligation.

After merged-state verification, the topic HEAD was confirmed reachable
from master. No worktree used the topic branch and no outstanding child
branch depended on it. The local topic branch was removed with
`git branch -d`. Unrelated branches and worktrees were left untouched.
No push, remote branch deletion or other remote mutation was performed.
