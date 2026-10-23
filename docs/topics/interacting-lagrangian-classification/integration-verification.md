# Master Integration Verification

The completed interacting-coordinate topic, its Lagrangian model connections
and the Euler-naturality successor are integrated into master after explicit
user direction. Euler naturality was first merged into its recorded non-master
parent; the full series was then merged into master. Both merges used
`git merge --no-ff` and completed without conflicts. Master had not advanced
beyond the series branch point. The separate documentation branches were not
included.

## Merged-State Checks

All six focused audits pass on the merged parent and again on master, using
3,989 build jobs per focused run. They collect transitive axioms and accept
only propext, Classical.choice and Quot.sound; layer checks are unchanged.

| Audit pair | Mathematical checks | Physical checks | Total checks |
| --- | ---: | ---: | ---: |
| Interacting coefficient presentation | 314 | 37 | 351 |
| Lagrangian model connections | 141 | 176 | 317 |
| Euler naturality | 310 | 9 | 319 |
| Total | 765 | 222 | 987 |

The serialized full `lake build` passes 8,041 jobs on master. Default proof
limits and dependency pins are unchanged. Advisory module-system import
notices and inherited repository warnings remain; no unresolved proof
diagnostic or new axiom exception is accepted.

```sh
LEAN_NUM_THREADS=2 lake build Math.RepresentationTheory.Audit.AuditInteractingLagrangian Physics.FieldTheory.Jets.Audit.AuditInteractingLagrangian Math.RepresentationTheory.Audit.AuditLagrangianModel Physics.FieldTheory.Jets.Audit.AuditLagrangianModel Math.RepresentationTheory.Audit.AuditEulerNaturality Physics.FieldTheory.Jets.Audit.AuditEulerNaturality
LEAN_NUM_THREADS=2 lake build
node tools/layout/check-layout.mjs
python3 tools/docs/check-topic-index.py
python3 tools/docs/check-work-metadata.py
node tools/docs/check-links.mjs
git diff --check
```

Builds use two threads, a 16 GiB address-space guard and a 540-second timeout.
Layout passes 2,544 modules. Navigation covers 168 topics and their outcomes.
Portable metadata checks 1,280 files. Link validation covers 1,288 Markdown
files, 8,321 local links and 156 fragments with zero errors. Whitespace checks
pass. The final record edits are documentation-only; no additional Lean build
was rerun after those edits. The merged-state proof checks above are unchanged.

## Scope And Source Review

The bibliography already records the final source versions and comparison
limits for Criado–Pérez-Victoria, Grzadkowski et al., Tong, Dreiner–Haber–Martin
and Sardanashvily. These were reconciled with the three topic registers before
integration; no literature premise or comparison scope is changed here.

The all-order result is an exact coordinate presentation, with closed
classifications for the specified polynomial-potential family. It is not a
universal terminating normal-form solver. Automatic density symmetry covers
compatible constant linear field/direction actions on finite local polynomial
densities, with no fixed degree or jet-order cutoff. Analytic action integrals,
nonlinear field transformations and geometric volume/Jacobian transport remain
outside this result. Existing input APIs are preserved.

No push or remote branch deletion is performed. The local Euler-naturality
and interacting-classification branches are safely deleted after merged-state
verification, ancestry and worktree checks. The earlier model-connection child
was already safely deleted after its parent integration. Historical branch
names remain in their topic records. Other branches and worktrees are retained.
