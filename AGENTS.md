# Repository Working Rules

## Start Here

- Read `git status --short --branch`, then the selected topic under
  [docs/topics](docs/topics/README.md). Read only its linked proof/source files.
- Follow [the workflow](docs/architecture/WORKFLOW.md). The original
  [CODEX_TASK](docs/topics/project-origins/materials/CODEX_TASK.md) is historical, not current
  instructions. Retained milestones and chronology are checkpoint evidence;
  do not append new work to them. Record verified topic integrations and settled
  stops in the short [topic outcome guide](docs/topics/_history/README.md),
  without dates or commit IDs; detailed status stays in each topic.
- Preserve unrelated changes and checked proofs. Do not invoke other LLMs
  unless the user explicitly authorizes delegation.
- In documentation math, do not use `\operatorname{...}`: it caused a macro
  rejection in the published GitHub rendering. Use `\mathrm{...}` for upright
  names instead, for example `\mathrm{Hom}`, `\mathrm{Sym}` and `\mathrm{diag}`.

## Lean Search And Inspection

- Use `rg` / `rg --files` first to locate declarations, imports and files.
- Do not use `lean-lsp-mcp`; the user has disabled the Codex MCP integration.
  Do not probe, start, reconnect or repair it unless explicitly requested.
- Inspect source and use targeted `lake env lean` / `lake build` checks for
  elaborated types, proof states and diagnostics. Confirm search misses with
  source inspection before inventing an API.
- Do not repeatedly report MCP unavailability; this is the intended workflow.
  Source inspection and doc-gen4 output do not replace builds or axiom audits.
  See [the detailed workflow](docs/architecture/LEAN_TOOLING.md).

## One Topic, One Record, One Branch

- Creating a top-level topic branch from `master`, and merging a topic branch
  back into `master`, require explicit user direction. Do not treat topic
  approval, a completed endpoint or a verified commit as merge authorization.
  This checkout uses `master`; do not rename it or switch the remote default.
- Name branches `proof/<topic>`, `audit/<topic>`, `docs/<topic>` or
  `refactor/<topic>`. Reuse a topic's existing branch when resuming it.
- Within an existing top-level topic branch, bounded child branches may be
  created and merged back into that topic branch at agent discretion. Record
  the parent exception and never use it to merge the parent into `master`.
- Record the integration target and working branch in
  `docs/topics/<topic>/README.md`. A bounded child of an unmerged topic may
  branch from and merge back into its parent, with that exception recorded.
  Never merge unrelated parent work into `master` as a side effect.
- Each topic owns its status, endpoint, remaining work, result and verification.
  Change that record when work finishes; do not move it into a global completed
  file. Short outcome links in `docs/topics/_history/` are the navigation-only
  exception; detailed state stays in the topic. Keep its overview short; split
  substantial phases/results into linked files.
- Commit coherent, verified milestones on the topic branch. Intermediate commits
  are not permission to merge incomplete work.

## Proof And Scope Gates

- Place sources by subject under `Math/`, shared physics under `Physics/`, and
  model applications under `GUT/`; see [the layout](docs/architecture/MODULE_LAYOUT.md).
  Math must not import Physics/GUT; Physics must not import GUT. Math-owned
  declarations use `Math.*`; canonical Physics declarations use `Physics.*`
  and model applications use `GUT.*`. Deprecated compatibility modules may retain
  registered legacy names. Subject namespaces need not repeat the full file path.
  Shared historical namespaces do not override declaration ownership.
- Preserve stable subject namespaces when subdividing directories. Public
  import/name changes require the registered compatibility shims, deprecations
  and old-client checks described in the layout policy.
- Register new files and audits in the appropriate aggregate (`Math.lean`,
  `Physics.lean`, or `GUT.lean`). Run `node tools/layout/check-layout.mjs` after
  source/import changes. Do not relax an import/axiom audit to permit a move.

- Freeze the statement, hypotheses, needed interfaces and stop condition before
  implementation. Do not silently add assumptions or recursively start a new
  foundational project. A counterexample or scoped feasibility decision is valid.
- Follow [the structural proof policy](docs/architecture/PROOF_ENGINEERING.md).
  Numerical or exhaustive per-case computation must not supply the main proof,
  even through kernel-checked generated certificates. Do not split repeated
  expansions into large families of near-identical lemmas/files to fit resource
  limits. Prove a shared structural theorem and derive the cases from it;
  small exact checks may only discharge identified supporting identities.
- Keep the project within exact symbolic/algebraic formalization and bounded
  repository-scale computational checks. Do not start or extend topics whose
  endpoint requires RGE evolution, nonperturbative QCD or hadronic matrix
  elements, lattice/Monte Carlo computation, or numerical simulation beyond
  lightweight reproducible scripts. Such results may appear only as explicit
  external inputs or documented boundaries; stop the formal result before
  them. Do not add computational environments or dependencies for that work.
- Keep Lean and dependency pins unchanged unless explicitly approved.
- Do not use `sorry`, custom axioms or audit allowlist exceptions to claim success.
  Approved literature inputs must remain explicit theorem parameters, with their
  sources and application conditions documented. Auditing an implication does
  not prove its premise. Preserve the E6 literature boundary and physical scope.
- Persist reusable audits in source control. Keep disposable build output out
  of source control and out of routine context.

## Verify And Integrate

- Treat a coherent commit as a checkpoint, not a default stopping point.
  Unless user judgment, new authority or a scope decision is required, continue
  autonomously through the recorded endpoint, verification and further coherent
  commits. Compact or summarize accumulated context as needed; context size alone
  is not a reason to stop or hand the topic back.
- Proof changes: run focused builds, strict transitive axiom audits and
  `lake build`; record commands, results and any residual warnings.
- Documentation-only changes: check local links and `git diff --check`; say
  explicitly that no Lean build was rerun. Do not invent a new proof baseline.
- For authorized README edits, review its graphs and tables in the same change.
  Update affected routes, names, counts and links together; regenerate affected
  assets and check rendering and ordinary-link alternatives. See
  [README maintenance](docs/architecture/WORKFLOW.md#readme-figures-and-tables).
- Keep topic literature sources documented. Before merging a topic, reconcile
  its references into [the literature list](docs/proof/RELATED_LITERATURE.md),
  updating existing entries where appropriate and preserving inspection limits.
- On completion, review the diff and assumptions and commit the verified topic.
  Merge into `master` only when the user explicitly directs it, using
  `git merge --no-ff <topic-branch>`, then recheck the merged result. If the
  target advanced, validate against it before integration. Bounded child-topic
  merges into their recorded non-`master` parent remain agent-discretionary.
- Do not integrate another contributor's dirty worktree or overwrite changes.
  Stop on unclear targets or semantic conflicts. Use a separate worktree for
  parallel work. Report integration failures rather than marking them merged.
- After a successful merge and merged-state verification, delete the local topic
  branch with `git branch -d` only after confirming its HEAD is reachable from
  the integration target, no worktree uses it, and no child work still needs it.
  Switch away from the branch before deletion. Retain historical branch names
  in topic records. Stop if safe deletion fails; force deletion, remote branch
  deletion, force-push, shared-history rewriting and remote pushes require
  separate authorization.
- Report the integration result, checks and remaining boundaries. Git commit
  IDs may be reported in the conversation; do not embed local commit IDs or
  work dates in maintained documents. Preserve external source and dependency
  revisions, bibliographic information and required attribution metadata.
