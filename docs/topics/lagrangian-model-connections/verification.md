# Verification

## Proof Gates

The focused audit build passes 3,971 jobs. The mathematical audit checks 141
declarations transitively; the physical audit checks 176, for 317 checks.
Only propext, Classical.choice and Quot.sound are accepted. Import-layer
checks reject Physics/GUT in Math and GUT in Physics.

The serialized full build passes 8,027 jobs. All newly added files are
registered in the appropriate aggregates. The new source files have no
remaining warnings; inherited repository warnings remain. Default Lean
elaboration limits and dependency pins are unchanged. No sorry, custom axiom
or audit allowlist exception is used.

```sh
LEAN_NUM_THREADS=2 lake build Math.RepresentationTheory.Audit.AuditLagrangianModel Physics.FieldTheory.Jets.Audit.AuditLagrangianModel
LEAN_NUM_THREADS=2 lake build
node tools/layout/check-layout.mjs
python3 tools/docs/check-topic-index.py
python3 tools/docs/check-work-metadata.py
node tools/docs/check-links.mjs
git diff --check
```

Builds use the frozen 16 GiB address-space and 540-second wall-clock guards.
Intermediate syntax expansion and implicit carrier reductions reached the
default heartbeat guard. Named semantic expansion lemmas, explicit source
instances and typed transports resolved them without raising limits.
The final literature check proves Euler-family equality for directly compiled
paper syntax and evaluation-preserving transport of its complete relations.
Literature dictionaries and artificial controls are Lean theorems imported by
the strict audits, rather than unchecked script output.

## Repository Gates

Layout passes 2,530 modules. Navigation passes 167 indexed topics and 167
outcome links with no pending exception. Metadata passes 1,274 portable files.
Local links pass 1,282 Markdown files, 8,272 inline links and 156 fragments with
zero errors. The diff whitespace check passes. Both guide snippets and their
quartic-target/coordinate-roundtrip consumers compile in a disposable Lean file.
Build logs and the guide-check file remain outside source control.

## Claims Review

- Existing direct/generated input definitions and dependency pins are unchanged.
- Registered models package their proved actions and certificates.
- The scalar/Weyl total density, independently specified Euler equations and
  full relations agree. All-order reconstruction and selected preimages are reused.
- This checkpoint used component Euler covariance. The
  [successor](../euler-naturality/verification.md) records the separate
  verification of semantic density-to-Euler naturality for constant linear actions.
- [Three source comparisons and artificial controls](literature-validation.md)
  pass in their documented conventions. No whole-paper count, reality quotient,
  quantum result or arbitrary finite normal-form solver is inferred.
- Bibliographic entries and external-source coverage links are reconciled;
  artificial checks and build details stay in this topic.


[Master integration verification](../interacting-lagrangian-classification/integration-verification.md)
records the final checks for the complete series.
