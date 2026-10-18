# Results And Verification

## Proved Connections

- `GradedSixQuarkComparison.equiv` identifies the actual specified `u²d⁴`
  exterior model sector with the degree-uniform separated quotient Hom at
  mixed degree `(6,0)`. The ordered bridge proves local/residual action equality,
  all species-preserving permutation relations and the converse typed exchanges.
- `GradedWeinbergComparison.onSMEquiv` identifies the actual SM `LLHH` model
  sector with the separated quotient Hom at `(2,2)`. Singleton species evaluation,
  tensor-unit removal and exterior/symmetric power transport are equivariant.
  `inputEquiv_pure` preserves generator evaluations without an extra factorial.
- Both comparisons to the existing explicit residual Hom have commuting
  extraction/reconstruction diagrams, both inverse laws and prohibition/nonzero
  equivalences. One-generation controls transfer to `Fin 2 → ℂ` and `ℂ`, respectively.

The generic classification constructs the new residual quotient. The old coordinate
classifications are comparison targets, not premises of the general theorem.
These results do not enumerate additional contents or extend literature coverage.

## Prerequisite Generalization

The six-quark assembly formerly expanded flavor vectors in finite bases.
Universal tensor lifting and `IndexedTensorSeparation.equiv` now give its
unchanged pure-tensor formula for arbitrary complex slot modules. The coordinate
inverse, typed-flavor Hom equivalence and physical-sector bridge no longer need
finite-dimensional up/down modules. The statistics relations are unchanged.

The LLHH sources' private additive-group instances are reducible to make the
existing and new exterior-power interfaces agree definitionally; their
mathematical hypotheses and normalization are unchanged.

Mathlib's `irreducible_def` packages the large physical equivalences with proved
definition equations. This prevents costly kernel reduction of their constructed
inverses; both equivalences and their definition equations are transitively audited.
No additional axiom or audit exception is introduced.

## Checked Milestones

- `lake build Physics.StandardModel.Operators.DeltaBTwoFlavorBridge`:
  successful, 3,287 jobs.
- Focused consumer builds: six quarks 3,325 jobs; LLHH 3,816 jobs, successful.
- `lake build Physics.StandardModel.Operators.Audit.AuditSixQuarkArbitraryFlavor
  Physics.StandardModel.Operators.Audit.AuditGradedSixQuarkComparison
  Physics.StandardModel.Operators.Audit.AuditGradedWeinbergComparison`:
  successful, 3,839 jobs; **41 strict transitive checks** (8 + 16 + 17).
  Only `propext`, `Classical.choice` and `Quot.sound` are permitted.
- Downstream compatibility: `lake build
  Physics.StandardModel.Operators.Audit.AuditLiSixQuarkBasis
  Physics.StandardModel.Operators.Audit.AuditLiSixQuarkFlavorBoundary
  Physics.StandardModel.Operators.Audit.AuditHeeckLeBasis`:
  successful, 3,373 jobs; 18 + 13 + 831 strict checks passed. Unused
  finite-dimensional section variables were removed from the affected
  Li/Heeck–Le bridges. Printed-span completeness still needs finite-dimensional
  D with dimension at most three, but not finite-dimensional U. Existing ledger
  conditions were corrected; no additional source locations were verified.
- Final serialized `lake build`: successful, **6,524 jobs**, no warnings or errors.
- `node tools/layout/check-layout.mjs`: **1,197 modules**, all checks passed.
- `node tools/docs/check-links.mjs`: **460 Markdown files / 3,081 local links /
  100 heading fragments**, no errors.
- `git diff --check`: passed.

The proof checkpoint is `checkpoint 01`. The topic meets its frozen stop condition;
no in-scope work remains. Master integration was explicitly requested on
stage 01; Git ancestry in `master` records the integration, independently of
the completed topic status.
Completed-result dossiers: [six quarks](../../proof/current/applications/Physics/GRADED_SIX_QUARK_COMPARISON.md)
and [LLHH](../../proof/current/applications/Physics/GRADED_WEINBERG_COMPARISON.md).

## Boundaries

Groups are arbitrary abstract groups and fermion flavor modules are arbitrary
complex modules. The six-quark result fixes the existing all-right `(2,4)` content;
its general target has typed constraints, not 25 free flavor coefficients.
The two-coordinate control is a one-generation specialization, not a general
dimension claim or printed ten-seed completeness statement.

LLHH retains one Higgs doublet with trivial residual action. Two symmetric Higgs
slots do not constitute a multi-doublet model. Neither connection supplies a
decision procedure for arbitrary residual groups, an all-degree cutoff, UV
matching, derivative/EOM/IBP classification or rates.
