# Verification

## Proof Endpoint

The [result](result.md) meets all three frozen phases: independent-species Hom
surplus to actual kernel splits, the actual-range physical qque bridge, and a
generic all-mass constructor. Gauge irreducibility derives copy factorization.
Model presentations and NoPairings conditions remain explicit application inputs;
no UV model or generated interaction is inferred from these checks.

Checks on the completed topic branch:

- `lake build Math.RepresentationTheory.Decomposition.Audit.AuditSpeciesCopySurplus Physics.FieldTheory.Mass.Audit.AuditPhysicalSpeciesCopySurplus`:
  passed, 3742 jobs. Persisted audits check 12 Math and 19 Physics declarations
  transitively; only `propext`, `Classical.choice` and `Quot.sound` are allowed.
  Import audits check current ownership and original SU5/SU6 module provenance.
- `lake build`: passed, 6625 jobs; no warning/error lines in the full-build log.
- `node tools/layout/check-layout.mjs`: passed, 1298 modules.
- `python3 tools/species-copy-surplus/audit_controls.py`: passed, six exact
  controls, including all 729 small integer 2×3 matrices, independent kernel
  directions, nontrivial C2 constituents, disjoint constituents, false converses
  and independent neutral Majorana sectors. These checks are not Lean premises
  or exhaustive UV-model checks; see the [script description](../../../tools/species-copy-surplus/README.md).
- `node tools/docs/check-links.mjs`: passed, 577 Markdown files, 3697 local
  inline links, 88 heading fragments, zero errors. The same read-only check was
  rerun outside the sandbox after its git subprocess hit `EPERM`.
- `git diff --check`: passed.

Review confirmed arbitrary H, independent finite physical species copies,
source semisimplicity only, actual original-mass radical support and the existing
SM/Lorentz/exterior semantic bridge. The mathematical kernel theorem additionally
permits arbitrary source carriers and any family index. No dependency pins,
custom axioms, audit exceptions or unrelated model records were changed.
No whole-radical extension or coefficient generation is claimed.

## Planning Checkpoint

Commit `checkpoint 01` froze the statement, staged plan and interface register.
Its documentation-only checks passed; no Lean build was rerun for that planning
checkpoint. The preceding integrated model topic's build belongs to its own
[verification record](../proton-protection-model-checks/verification.md).

User-directed master merge `checkpoint 02` passed the serialized full build
(6625 jobs, including the persisted 31 checks), layout (1298 modules),
all 18 exact controls, links (584 files, 3719 links, 88 fragments) and
`git diff --check`. The local topic branch was removed after reachability
and worktree checks. No remote push was requested or performed.
