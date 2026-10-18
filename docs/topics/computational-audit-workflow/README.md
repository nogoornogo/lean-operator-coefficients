# Computational Audit Workflow

- ID: computational-audit-workflow
- Status: completed
- Result type: documentation.
- Working branch: `docs/computational-audit-workflow`.
- Integration target: `master`.

## Endpoint And Scope

Add computational cross-check rules to
[WORKFLOW.md](../../architecture/WORKFLOW.md): rerun triggers, reproducibility,
result recording, failures/disagreements and the distinction from Lean proofs.
Do not change proof statements, test implementations, AGENTS.md or dependency
pins. Existing topic/test documentation supplies the individual commands.

## Verification

`node tools/docs/check-links.mjs` passed (253 Markdown files, 1382 links), as
did `git diff --check`. This is documentation-only; no Lean build or
computational test was rerun and no proof verification baseline was changed.
Git ancestry records integration into the target branch.
