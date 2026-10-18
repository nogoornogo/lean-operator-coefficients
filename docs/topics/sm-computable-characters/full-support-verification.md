# Complete structural support verification

Branch `proof/sm-computable-characters`, resume base `checkpoint 01`, integration
target `master`; no merge or push. See [results](full-support-results.md).

## Proof checks

Commands use the existing guarded runner, one Lean thread, 6 GiB sampled
process-group RSS and 4 GiB host reserve. Final focused/audit wall caps are
90 s; the signature probe cap is 30 s. Builds are serialized.

```text
env LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build \
  --timeout-seconds 90 --rss-limit-gib 6 --min-available-gib 4 MODULE /tmp/LOG
```

- New U/D and lepton Math/Physics adapters passed focused builds. The final
  `Physics.StandardModel.Operators.SMJointHiggsSupport` build passed all
  4603 jobs; guarded 4.8 s, sampled peak 5155700 KiB. Its dependencies include
  the actual all-species catalogue, generation/species source comparison and
  complete finite joint composition.
- `Math.RepresentationTheory.Audit.AuditStructuralExteriorSupport` passed
  2018 strict transitive checks, 4345 jobs; guarded 6.5 s, sampled peak
  5416276 KiB.
- `Physics.StandardModel.Operators.Audit.AuditSMStructuralSupport` passed
  346 strict transitive checks, 4650 jobs; guarded 5.0 s, sampled peak
  5504968 KiB. Total structural checks: 2364. Every named declaration in
  the new modules and both new `FiniteSourceSums` helpers is registered.
- A disposable signature probe confirmed that both final original-space
  theorems quantify only over p, nonzero cyclic modulus k, q,l and h,d.
  There is no hidden presentation, branching, Weyl or occurrence premise.
  `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.
  Guarded 3.5 s, sampled peak 5045084 KiB.
- Default `lake build`, including **Math, Physics and GUT**, passed all
  **7320 jobs**, zero warnings/errors. The serialized runner used one Lean
  thread, a 10 GiB process-group guard, 4 GiB host reserve and 300 s wall cap.
  Guarded 11.0 s, sampled peak **6671028 KiB**, `stopped=False`.

Development corrected ordinary elaboration errors (data-valued finite
species dispatch and explicit tensor-functional extensionality). Direct
concrete tree transport reached the unchanged 200000-heartbeat default;
keeping the indexed dictionary abstract in `indexedDecomposition` and using
`equivOfEq` fixed it. The actual source comparison then built in 3.6 s.
No proof limit was raised. One dependency-rebuild probe hit its 120 s wall
cap (sampled peak 4985148 KiB); the serialized resumption used a 300 s cap.
No RSS/host-reserve guard triggered. A temporary edit to the foundational
coefficient-transport file was restored exactly; it is absent from the diff.
All disposable probes and build logs remain outside source control.

## Repository checks

- `node tools/layout/check-layout.mjs`: **1934 modules**, layers, local
  imports, cycles, aggregates and relocation audits pass.
- `node tools/docs/check-links.mjs`: **955 Markdown files, 5867 local links,
  111 fragments, zero errors** at the final dossier check. The existing
  read-only `git ls-files` subprocess required sandbox escalation; the
  checker was unchanged.
- `python3 tools/exact-rank/check-retired-certificates.py`: **19 snapshot
  hashes verified; 15 retired numerical modules absent from active imports**.
- New/changed source token and proof-limit scans, named-declaration audit
  coverage and `git diff --check` pass.
- Dependency/toolchain pins and the root README are unchanged. No retired
  numerical proof was built or imported; no multiplicity/rank numeral or
  assignment enumeration is used in the support theorem.

The [proof dossier](../../proof/current/applications/Physics/SM_STRUCTURAL_QL_SUPPORT.md)
and both assumptions ledgers state the actual fixed-input scope. Original
endpoint 2 is complete for the existing scalar q/l action; arbitrary residual
representations retain the parameterized endpoint-1 `Allowed(T)` interface.
