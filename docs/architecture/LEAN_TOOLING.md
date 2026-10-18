# Lean Search And Inspection Workflow

Use source search, command-line Lean checks and generated documentation for
complementary tasks. None of them changes the proof acceptance gates in
[AGENTS.md](../../AGENTS.md).

## Routine Work

1. Locate the likely file, declaration or import with `rg --files` and `rg`.
   Search the relevant domain first; broaden to other project modules and
   pinned package sources when necessary.
2. Read the relevant declarations, surrounding `variable` commands and
   instances. When the elaborated type matters, use a bounded scratch Lean
   file with the relevant imports and `#check` / `#print`, checked with
   `lake env lean`. Keep scratch files and output out of source control.
3. Use targeted `lake env lean` / `lake build` checks for proof diagnostics
   and remaining goals. Restrict diagnostic output to the relevant file and
   positions; avoid repeatedly dumping full sources or build logs.
4. Confirm a search miss against relevant project and pinned dependency
   sources before inventing an API. Source search alone does not resolve
   elaboration, coercion or typeclass questions.
5. After edits, run the required focused builds, persistent strict transitive
   axiom audits and full `lake build`. A closed goal or clean LSP response is
   not a project-wide proof certificate.

## Environment

Keep the pinned toolchain unchanged and use the current worktree's Lake project.
Leave user-owned editor services alone. Do not install/update dependencies or
change global agent settings for a lookup.

## Generated Documentation

Keep [doc-gen4](DOCUMENTATION.md) for human-facing API browsing and overview.
Do not regenerate all dependency documentation for each proof lookup. It may
reflect an older build; source and current Lean elaboration take precedence.
