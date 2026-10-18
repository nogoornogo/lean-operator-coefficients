# TauCeti And Lean Upgrade

- ID: tauceti-lean-upgrade
- Status: completed
- Result type: compatibility verification
- Working branch: `audit/tauceti-lean-upgrade`
- Integration target: `docs/milestone-documentation`
- Parent exception: this bounded upgrade branches from the unmerged documentation
  topic so that the current source relocation and documentation are tested.
  It does not authorize integrating the parent into master.

## Endpoint And Scope

Validate the current project on TauCeti's observed main revision
`b9e2e182804073eb92718b68a9baf37df8e189bd`, its Lean `v4.35.0-rc3`, and mathlib
`1a547d8a48a8fa7877d2decb69d7294723bb0187`. The previous toolchain was
`v4.34.0-rc2`, TauCeti `355c248fa848acd70c2a4b412ca5f53d37b0402a`, and mathlib
`30a58f795ae8c95b8299fe3c9ded1e6498a9e9fe`.

The user explicitly authorized a dependency/toolchain upgrade and a new branch.
Preserve theorem statements, trust boundaries and strict axiom allowlists.
Port API/tactic changes within existing proofs. A required new mathematical
premise or foundational project is a scope decision, not an implicit upgrade.

## Deliverables And Acceptance

1. Pin a mutually compatible Lean, mathlib and TauCeti dependency set.
2. Build affected imports and all three project aggregates, including audits.
3. Resolve bounded compatibility failures; record remaining warnings and failures.
4. Check layout, documentation links and relevant existing script tests.
5. Align the optional docbuild configuration where a compatible release exists.
6. Commit the verified result, or a concrete reproducible compatibility blocker.

## Work And Open Obligations

Follow-up authorized: eliminate project deprecation and lint warnings without
disabling linters, weakening audits, or adding mathematical premises.
Local `omit` scopes remove automatically included, unused section hypotheses;
these helper statements become more general, with downstream builds required.
Inventory the verified build diagnostics, apply API/style migrations, and rerun
the full build. Dependency-owned warnings are tracked separately.

- Matching toolchain installed; root and docbuild manifests refreshed.
- Focused compatibility checks passed for Finsupp transport, multiplicity matrices,
  local logarithms, path subdivision, E6 generators and SU realification.
- Full build and its persistent audits passed after compatibility fixes.
- Warning cleanup and its final full-build verification passed with zero
  warnings and zero errors. Ready for integration into the recorded parent;
  no master merge is authorized.

## Result And Verification

Upstream pins inspected directly with Git. Root README claims and theorem
assumptions are unchanged. Compatibility edits account for:

- `Finsupp.mapDomain_apply_of_injective` replacing the former injective API;
- representation and quadratic-map declarations moving out of `TauCeti` namespaces;
- explicit scalar-field arguments for local logarithm inverse theorems;
- the linear-character module splitting into `LinearCharacter.Basic`;
- the subpath composition theorem moving to mathlib;
- E6 minuscule matrix definitions factoring through `MinusculeWeightTable`;
- removal of proof steps now closed by `convert`/`norm_num`, and redundant `dsimp`;
- consistent finite-index normalization before `linear_combination`;
- explicit linear-map/equivalence zero lemmas to avoid generic typeclass-search
  timeouts in the E6 complexification and six-quark witness proofs.

The E6 carrier audit now checks the generalized `MinusculeWeightTable` rational
Serre and lattice-preservation declarations, instead of removed E6-specific
wrappers. Its E6 specialization and all 38 axiom checks pass. No audited
obligation was dropped and the standard axiom allowlist is unchanged.

The optional doc-gen4 executable builds successfully (194 jobs) with its matching
`v4.35.0-rc3` release. Full HTML generation is not part of this check.
Verification at stage 01:

| Check | Result |
| --- | --- |
| `lake build` | Passed, 6,254 jobs, including Math/Physics/GUT and persistent audits |
| `(cd docbuild && lake build doc-gen4)` | Passed, 194 jobs |
| Root/docbuild shared dependency revisions | Identical |
| `node tools/layout/check-layout.mjs` | Passed, 1,015 modules |
| `node tools/docs/check-links.mjs` | Passed, 372 Markdown files, 2,501 links, 76 fragments |
| `node --test tools/docs/test-check-links.mjs tools/layout/test-check-layout.mjs` | 14/14 passed |
| `python3 -m unittest discover -s tools/e6 -p 'test_*.py'` | 10/10 passed |
| `python3 tools/qque/audit_one_generation.py` | 4/4 passed |
| `python3 tools/delta-b-two/conventional-probes.py` | Probe inverse and all 225 monomial controls passed |
| `git diff --check` | Passed |

Initial full-build attempts exposed the compatibility changes listed above;
the final full build passed. Focused builds were also run on the affected
modules. Existing exact computational scripts remain regression checks, not
Lean proof oracles. No theorem hypotheses or resource ceilings were increased.

At the initial compatibility checkpoint, 353 warnings remained for deprecated
APIs/imports and unused/style lints. The user then authorized warning cleanup.
This migrates complex imports and tensor induction, removes redundant tactics
and simp arguments, adopts current local-instance syntax, marks inner-product
core definitions `instance_reducible`, and drops unused section hypotheses.
The new tensor induction API handles zero internally; its obsolete zero
branches are removed, not replaced by unproved cases. Lean remains a release
candidate, now `v4.35.0-rc3`; no stability beyond the pinned versions is claimed.
Root README claims remain unchanged; helper hypothesis relaxation is recorded
in the [Math assumptions ledger](../../proof/current/inputs/Math/ASSUMPTIONS.md).

### Warning Cleanup Verification

The final `lake build` passed (6,253 jobs, including all aggregates and persistent
strict audits), with **zero warning/error diagnostics**. This replaces the
353-warning baseline, including further warnings exposed during migration.
No linter was disabled, no audit allowlist was relaxed, and no dependency pins
or proof resource limits were changed by the cleanup.

Focused `lake env lean` checks passed without warnings for `Sl3HighestWeight`,
`HaarAveraging`, `OneDimensionalUnitaryCharacter`,
`CompactRepresentationUnitarization` and `ContinuousSU6Unitarization`.
Layout (1,015 modules), links (372 files, 2,503 links, 76 fragments), the 14 Node
tests, the 10 E6 tests, the 4 qque tests, all 225 six-quark monomial controls,
and `git diff --check` passed again. The optional doc-gen4 executable was not
rebuilt for this source-only cleanup; its upgrade check above remains separate.

Intermediate runs caught migration errors and newly exposed unused hypotheses.
An accidentally overlapping build also caused missing generated-file errors;
the duplicate was stopped, all build processes were allowed to finish, and
verification was repeated sequentially. Only the final successful sequential
build is the warning-free acceptance result. Disposable logs are not committed.

## References

- [TauCeti pinned revision](https://github.com/TauCetiProject/TauCeti/tree/b9e2e182804073eb92718b68a9baf37df8e189bd)
- [Lean tooling](../../architecture/LEAN_TOOLING.md)
- [Build instructions](../../architecture/BUILD.md)
