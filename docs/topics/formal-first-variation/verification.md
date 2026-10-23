# Verification

Working branch: `proof/formal-first-variation`; integration target:
`proof/gauge-covariance-engineering`, under its recorded bounded-child exception.
The initial parent worktree was clean. This verified child remains unmerged;
no master integration or remote mutation is included.

## Proof Gates

The contract was frozen before implementation. Ordered derivative iterates,
actual polynomial coefficient extraction and trace cyclic IBP close the primary
routes. Both consumers prove equality of differential Euler/EOM ideals in
addition to the contracted quotient identities. No assumption, custom axiom,
resource override, audit exception or dependency pin was added.

All heavy checks used four Lean threads, a 540-second timeout and inherited
16 GiB per-process address-space bound; default Lean limits were retained.

```sh
LEAN_NUM_THREADS=4 lake build Physics.FieldTheory.Jets.YangMillsFirstVariation Physics.FieldTheory.Jets.ScalarFirstVariation
LEAN_NUM_THREADS=4 lake build Math.Algebra.Audit.AuditFirstVariation Physics.FieldTheory.Jets.Audit.AuditFirstVariation
LEAN_NUM_THREADS=4 lake build
```

Consumer build passed, 3285 jobs. Final focused audit build passed, 3288 jobs:
36 Math and 31 Physics public declarations, each checked with transitive
`Lean.collectAxioms`, permitting only `propext`, `Classical.choice` and
`Quot.sound`. Math rejects Physics/GUT imports; Physics rejects GUT imports.
The explicit audit inventories cover every new public definition, abbreviation
and theorem. Full build passed, 7669 jobs.

Residual warnings are dependency module-system import recommendations and
replayed existing warnings; no new unused-section-variable warning remains.
No `sorry`, new axiom or weakened import/axiom audit is used.

## Repository Gates

- `node tools/layout/check-layout.mjs`: passed, 2175 modules.
- `python3 tools/docs/check-topic-index.py`: passed, 155 indexed topics with outcomes.
- `python3 tools/docs/check-work-metadata.py`: passed, 1161 portable files.
- `node tools/docs/check-links.mjs`: passed, 1169 Markdown files, 7436 local links and 125 fragments.
- `git diff --check`: passed.

The bibliography, topic source roles, proof dossiers and assumption ledgers
record the same algebraic scope. Existing generic EOM APIs and old checked
sources are unchanged. Documentation was reconciled after the final successful
Lean build; those documentation-only edits did not require another Lean build.

## Final Master Integration

The [merged-state record](../derivative-ibp/master-integration.md) supersedes
the earlier unmerged integration status. The original proof endpoints and
checks above remain checkpoint evidence; all recorded parent merges and the
master merge are verified without changing theorem assumptions.
