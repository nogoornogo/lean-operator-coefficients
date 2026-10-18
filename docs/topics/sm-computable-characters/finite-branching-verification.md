# Finite branching verification

Branch `proof/sm-computable-characters`, starting from `checkpoint 01`. All Lean
builds are serialized with `LEAN_NUM_THREADS=1`, unchanged default proof
options and this existing guard:

```sh
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build \
  --rss-limit-gib 6 --min-available-gib 4 MODULE /tmp/finite-branching-MODULE.log
```

The 300-second default timeout and memory thresholds are unchanged. Sampled
process-group peaks are diagnostics, not hard memory limits or proof inputs.

## Focused proofs and audits

- `Math.RepresentationTheory.SU2FiniteBranching`: passed, 5.5 s and
  4874840 KiB before the final transport wrapper; the final wrapper is also
  checked by the later SM consumer build.
- `Physics.StandardModel.Operators.SMFiniteConstituentSupport`: passed in the
  guarded consumer build, 4.5 s for this module; its actual compact/Higgs iff
  has no Weyl premise.
- `Physics.StandardModel.Operators.SMFiniteWeakBranching`: final passed,
  4311 jobs, 9.0 s and 5039068 KiB including the updated SU2 branching module.
- `Math.RepresentationTheory.Audit.AuditStructuralExteriorSupport`: passed,
  4066 jobs, 8.8 s and 5215756 KiB; **66 strict transitive checks**, including
  all new generic branching/coupling interfaces, and unchanged layer and
  numerical-import rejection.

During development, passing a concrete model equivalence's underlying map
and surjectivity separately hit the default heartbeat limit. A symbolic
`transport_bound` wrapper, with the source carrier left abstract, resolved
both general and constant-species applications. The final SM weak module
built in 3.3 s without raising the heartbeat/recursion or memory budgets.
An explicit restriction helper in `BoundedTorusWeights` keeps the same
transport symbolic across the group map. Other development fixes were an
explicit continuity import, a twist namespace, and equivalence orientation.

- `Physics.StandardModel.Operators.Audit.AuditSMStructuralSupport`: passed,
  4369 jobs, 67.6 s and 5374640 KiB, including rebuilding its changed existing
  dependencies; **148 strict transitive checks**. The original layer and
  numerical-import rejection are unchanged.

The two audits total **214** checks, permitting only `propext`,
`Classical.choice`, `Quot.sound`. Final focused logs have no warnings or errors.
Six new proof modules and the restriction helper are registered and audited.
No retired numerical certificate was restored or run.

## Aggregate checks

The following guarded aggregate commands also used
`MIMALLOC_PURGE_DELAY=0 MIMALLOC_ARENA_EAGER_COMMIT=0`, as in the previous
verification, to reduce allocator retention without changing proof options
or the memory threshold:

| Target | Result | Time | Sampled group peak (KiB) |
| --- | --- | --- | --- |
| `Math` | passed, 6020 jobs | 22.5 s | 6200508 |
| `Physics` | passed, 5028 jobs | 186.6 s | 5672572 |
| `GUT` (the configured default library) | interrupted at the unchanged 6 GiB threshold | 5.1 s | 6423368 |

The GUT attempt is the default-library build, not a successful full `lake
build`. It reached the root aggregate after replaying dependencies. The
unchanged root memory gate remains outstanding; it is separate from the
proved finite-branching endpoint and from the open joint occurrence rule.
No budget was raised, and the unchanged failed root import was not retried.

## Repository checks

- `node tools/layout/check-layout.mjs`: 1694 modules; layers, imports, cycles,
  aggregate coverage and relocation checks passed.
- `python3 tools/exact-rank/check-retired-certificates.py`: 19 hashes match,
  15 retired modules remain absent, and there are no active retired imports.
- `node tools/docs/check-links.mjs`: 878 Markdown files, 5448 local links,
  109 fragments and zero errors.
- The six new proof sources have no `sorry`, custom axiom, `native_decide` or
  `implemented_by`; `git diff --check` passed.

The final `lake --no-build build Math Physics` check, also naming both strict
audit roots, passed with all targets up to date (6611 jobs). The default
`lake --no-build build` returned 3 with exactly `GUT` stale (7062 graph jobs).
This confirms the recorded root aggregate boundary; no other target remains
unbuilt in that graph.

Lean/dependency pins, root README, CSV data and archive snapshots are unchanged.
Source/theorem, assumption and scope review passed, as did staged diff checks.
The verified proof milestone is committed on the existing topic branch;
full default-build acceptance remains outstanding. No merge or push is made.
