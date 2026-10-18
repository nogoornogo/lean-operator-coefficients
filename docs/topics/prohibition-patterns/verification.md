# Verification

Planning baseline: master checkpoint 01, after no-ff merge checkpoint 02 of input API
checkpoint 03. Merged full build passed 6686 jobs, strict API audits 31 declarations,
layout 1359 modules and links 656 files / 4061 links / 91 fragments.
These checks concern the preceding API, not the new planned patterns.

## Pattern Implementation — stage 01

- Planning commit: checkpoint 04; scope frozen before source changes.
- Focused source build passed 3948 jobs.
- `lake build Math.RepresentationTheory.Audit.AuditProhibitionPatterns Physics.StandardModel.Operators.Audit.AuditProhibitionPatterns`:
  passed 3951 jobs; 17 strict transitive checks (2 Math, 15 Physics), with
  only propext, Classical.choice and Quot.sound allowed. Layer audits passed.
- Serialized `lake build`: passed 6690 jobs, including registered new audits
  and all aggregate builds. Existing diagnostics were replayed; the new source
  and audit builds produced no warnings.
- `node tools/layout/check-layout.mjs`: passed 1363 modules.
- `node tools/docs/check-links.mjs`: passed; final counts recorded below.
- `git diff --check`: passed.

An initial unused Fintype derivation for the target enum failed elaboration;
Fintype was removed because arbitrary indexed unions do not need it. No
assumption, dependency pin or audit allowance was changed to resolve the error.

Statement review retained actual quotient nontriviality for scalar/cyclic
necessity, explicit semisimplicity for constituent criteria, and distinct
mixed-field/dipole coefficient domains. The DGT joint example uses one UV
Circle group; restriction preserves its baryon coefficient linear map.
No new full-LFV, UV classification or literature-wide claim is made.
The English catalogue/source register and per-layer assumptions agree with
the checked statements. The bounded stop condition is reached.

Final documentation check: 661 Markdown files, 4087 local inline links,
91 heading fragments, zero errors. The read-only link checker used escalation
for git subprocess access. No remote push or new-topic master merge occurred.

## Authorized Master Integration — stage 01

No-ff merge `checkpoint 05` integrates topic `checkpoint 06` and plan `checkpoint 07`.
Merged-state `lake build` passed 6690 jobs, including 17 strict pattern checks
(2 Math, 15 Physics). Layout passed 1363 modules; documentation links passed
661 files / 4087 local links / 91 fragments; git diff check passed.
Integration record edits were documentation-only; no further Lean build was
needed after those edits. Topic HEAD is reachable from master, no worktree
uses its branch, and no child work needs it. The local topic branch is safely
deleted after verification. No remote push or remote branch deletion occurred.

## Reader-Facing README Update

At the user's request, the root README now introduces the representative
prohibition patterns in place of the extended Delta B=1-specific discussion.
It summarizes the five generic routes, links the twelve-row catalogue and
retains short links to the specialized qque/SU6 results. The three main
results and verified-sector section retain their existing emphasis.
Documentation-only: local link check passed 661 files / 4088 links /
91 fragments; git diff --check passed. No Lean build was rerun and no new
proof verification baseline is claimed. The unrelated untracked docs.zip was
left untouched.
