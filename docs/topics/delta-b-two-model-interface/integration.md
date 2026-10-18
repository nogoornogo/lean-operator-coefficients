# Delta-B = 2 integration

The user authorized documentation review and integration at stage 01.
The recorded order is `proof/delta-b-two-model-interface` into
`proof/delta-b-two-conventional-basis`, then that parent into `master`.
The proof endpoint is commit `checkpoint 01`; the parent endpoint is `checkpoint 02`.

The documentation review marks the original feasibility decision as historical,
links the later completeness/normalization/input results, and records that
all-chirality generalization is deferred. It introduces no new theorem or
physical prediction. Documentation checks do not create a new Lean baseline.

Integration succeeded without conflicts. Branches are retained; no remote
push was performed.

## Pre-merge verification

- Documentation-only edits passed local links and `git diff --check`. No Lean
  build was needed for those prose changes; the integration checks below rerun
  the existing proof package, rather than claiming a new theorem baseline.
- Focused builds of `AuditSixQuarkConventionalBasis`,
  `AuditSixQuarkFlavorResidualHom`, `AuditDeltaBTwoModelInterface`,
  `AuditSixSlotSpeciesSum`, `AuditSixSlotSpeciesTransport` and
  `AuditMultilinearInvariantHom` passed: 148 strict transitive axiom checks
  in total, with unchanged allowed axioms (3251 jobs).
- `lake build` passed (5971 jobs). Existing dependency warnings were replayed.
- `python3 tools/delta-b-two/conventional-probes.py` passed the probe inverse,
  determinant, conventional basis and all 225 Grassmann Fierz regression cases.
  This regression is not a trusted premise of the Lean proofs.
- Layout passed (918 modules); links passed (341 files, 2082 links,
  33 heading fragments, no errors).
- `master` at `checkpoint 03` is an ancestor of the working branch; the recorded
  parent target remains at `checkpoint 02`. No target advancement requires adaptation.

## Integration and merged-state verification

- Documentation review: `checkpoint 04` on the model-interface topic branch.
- Child into recorded parent: merge `checkpoint 05` on
  `proof/delta-b-two-conventional-basis`; its full `lake build` passed
  (5971 jobs).
- Parent into `master`: merge `checkpoint 06`. Both merges used `--no-ff`.
- On merged `master`, the same six focused audit targets passed all 148
  strict checks (3251 jobs); full `lake build` passed (5971 jobs).
  Allowed axioms and dependency pins are unchanged. Existing dependency
  linter warnings remain; no new proof source was changed during this review.
- The conventional probe/Fierz regression, layout check (918 modules),
  local links (341 files, 2082 links, 33 fragments) and `git diff --check`
  all passed on merged `master`.
- This final verification-record update is documentation-only. Links and diff
  checks are rerun without another Lean build; the merged proof baseline above
  is unchanged.
- The completed endpoint remains the derivative-free all-right degree `(2,4)`
  classification, its conventional normalization, and typed multiplicity/actual
  field transport. All-chirality generalization is deferred; UV matching,
  RGE, hadronic matrix elements and rates are not proved.
