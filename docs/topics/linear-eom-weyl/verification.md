# Linear EOM And Weyl Verification

The parent includes the explicitly authorized jet/spurion merge. Its merged
state passes the 3416-job focused closure (97 strict checks), 7618-job full
build, 2124-module layout and document checks. Those are retained integration
evidence, not a proof baseline for this new topic.

The new [contract](plan.md) is frozen before implementation on
`proof/linear-eom-weyl`. The parent is `proof/derivative-ibp` and remains
unmerged into master. Record this topic's proof gates and limits here as they
are checked. No linear-system or Weyl EOM theorem is claimed by this checkpoint.

## Successful Proof Endpoint

The [result](results.md) fulfills the contract, with the source/dual Pauli
orientation correction explicitly recorded there. Common polynomial-descendant
closure recovers the original scalar relations and shifts. The actual
exterior/symmetric quotient algebra, finite image grades and inverse
equivariant EOM/IBP source comparison are proved. Bounded finite-residual
evaluation permits intrinsic local component actions. The physical Weyl seed
covariance is discharged, rather than passed as an unproved model premise.
Both first-order seeds are nonzero off shell; descendants and wave consequences
vanish on shell. Null-polarization probes prove higher-jet survival in the
generator, exterior and actual mixed algebras before IBP.

Focused endpoint and audit command:

```sh
LEAN_NUM_THREADS=4 lake build Math.Algebra.Audit.AuditLinearJetEquation Physics.FieldTheory.Jets.Audit.AuditWeylLinearEquation
```

It passes **3414 jobs**, with **94 Math** and **51 physical** checks,
**145** total. Every new named public declaration has a persistent explicit
entry and is audited transitively. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted. Math rejects Physics/GUT imports; the physical
audit rejects GUT imports. No existing audit policy or proof is relaxed.

Full aggregate command:

```sh
LEAN_NUM_THREADS=4 lake build
```

It passes **7628 jobs**, including all Math, Physics, GUT and old/new audit
targets. Heavy checks use four Lean threads, a 540-second timeout and an
inherited 16 GiB per-process address-space guard (`resource.RLIMIT_AS`).
One focused attempt ended with the host error `failed to create thread:
Resource temporarily unavailable`; rerunning under the same guard succeeds.
This was an execution-resource interruption, not a theorem counterexample.
Disposable logs/guard wrappers remain outside source control. Default
heartbeats, recursion/kernel limits and root/docbuild dependency pins stay
unchanged. Explicit maps, pointwise pullback and projection/coercion equations
resolve elaboration without raising limits. New-module residual warnings
are module-system recommendations; existing project warnings remain.
No `sorry`, custom axiom, external physical completeness premise or allowlist
exception is introduced. A conditional generic seed theorem is distinguished
from its actual proved Weyl instantiation.

## Final Structural And Document Gates

- `node tools/layout/check-layout.mjs`: **2134 modules**, with layer/import,
  cycle, aggregate and relocation gates passing.
- `node tools/docs/check-links.mjs`: **1135 Markdown files**, **7233** local inline
  links and **125** heading fragments; zero errors. The unchanged checker
  runs in a permitted context for its read-only Git subprocess.
- `python3 tools/docs/check-topic-index.py`: **150 topics**, all indexed and
  linked to outcomes; no pending exception.
- `python3 tools/docs/check-work-metadata.py`: **1127** portable files,
  source metadata retained. `git diff --check`: passes.
- Root/docbuild toolchain and dependency-pin diff is empty. The bibliography,
  source register and Math/Physics assumption ledgers agree with the actual
  one-chiral-system scope and the unproved comparison boundaries.

The successful stop is on `proof/linear-eom-weyl`, targeting the unmerged
`proof/derivative-ibp` parent. Final documentation edits follow the successful
full build and change no Lean theorem or dependency; no extra Lean build is
rerun for those documentation-only edits. A verified coherent commit completes
the original endpoint; it preceded the integration recorded below.

## Integration Into The Derivative/IBP Parent

The verified `proof/jet-eom-completion` child was first integrated into this
branch and reverified: 255 focused strict checks, 3424 jobs and the 7637-job
full build. Its own [integration record](../jet-eom-completion/verification.md)
owns the details. The combined branch was then merged with
`git merge --no-ff proof/linear-eom-weyl` into the recorded
`proof/derivative-ibp` parent. The target was clean and had no independent
advance. The merge preserves history and has no semantic or textual conflict.

On the final parent, the nine-audit closure covers direction/scalar EOM,
jet/spurion, common linear equations, left-Weyl and kernel/conjugate extensions:
3444 jobs and 625 strict transitive checks. Full `LEAN_NUM_THREADS=4 lake build`
passes 7637 jobs under the unchanged four-thread, 540-second and 16 GiB
per-process guard. Layout passes for 2143 modules. Local links, all 151 topic
and outcome links, portable metadata and diff checks pass. The source/assumption
statements, bibliography and pins match the verified combined branch.

The [parent record](../derivative-ibp/verification.md) owns the final combined
integration gate. Documentation updates follow that proof gate and do not
trigger another Lean build. This is integration into the unmerged topic parent,
not master integration or a remote update. Historical branch names are retained.

After merged-state verification, the local kernel/conjugate child and this
local branch were safely deleted with `git branch -d`. Their HEADs are reachable
from their recorded integration targets, no worktree uses them and no pending
child work requires either branch. The final checkout is `proof/derivative-ibp`.
