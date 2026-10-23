# Authorized Master Integration

The user explicitly requested integration into master of the completed
scalar coefficient theorem and literature verification. Its required
verification foundations were still on `proof/derivative-literature-foundations`.
The authorized scope therefore contains this parent, the already integrated
finite C1/C2 child and the completed quartic order-four child. No unrelated
topic branch is included.

The worktree was clean and master had no independent advancement relative
to this stack. Before integration, fifteen foundation/scalar audit sources
were freshly elaborated with 1620 strict transitive checks passing. The
quartic child was merged with `--no-ff` into its recorded parent, followed
by fresh focused audits, full build, exact diagnostics and repository gates;
the [child integration record](../scalar-quartic-four-completeness/integration.md)
owns that evidence.

## Verified master merge

The verified parent was merged into master without conflicts, preserving
both topic histories:

```sh
git switch master
git merge --no-ff proof/derivative-literature-foundations
```

All fifteen audit sources were freshly elaborated again on master. These
inventories cover definitions, instances and supporting declarations, not
1620 independent new theorems:

| Audit source | Strict transitive checks |
| --- | ---: |
| Math/Algebra/Audit/AuditScalarCompletenessHelpers.lean | 45 |
| Math/Algebra/Audit/AuditScalarQuarticFour.lean | 80 |
| Math/RepresentationTheory/Audit/AuditDerivativeLiteratureFoundations.lean | 286 |
| Math/RepresentationTheory/Audit/AuditExtendedDerivativeChecks.lean | 155 |
| Math/RepresentationTheory/Audit/AuditNonDerivativeInputChecks.lean | 62 |
| Math/RepresentationTheory/Audit/AuditScalarCompletenessChecks.lean | 18 |
| Math/RepresentationTheory/Audit/AuditScalarTwoSpeciesCompleteness.lean | 159 |
| Physics/FieldTheory/Jets/Audit/AuditExtendedDerivativeChecks.lean | 52 |
| Physics/FieldTheory/Jets/Audit/AuditLiteratureFoundations.lean | 155 |
| Physics/FieldTheory/Jets/Audit/AuditLiteratureRecheck.lean | 28 |
| Physics/FieldTheory/Jets/Audit/AuditNonDerivativeModelChecks.lean | 22 |
| Physics/FieldTheory/Jets/Audit/AuditScalarCompleteness.lean | 123 |
| Physics/FieldTheory/Jets/Audit/AuditScalarCompletenessChecks.lean | 31 |
| Physics/FieldTheory/Jets/Audit/AuditScalarQuarticFour.lean | 370 |
| Physics/FieldTheory/Jets/Audit/AuditScalarQuarticLiterature.lean | 34 |

All 1620 checks pass with only propext, Classical.choice and Quot.sound
allowed and source-layer restrictions retained. Each file uses the existing
16 GiB disposable address-space wrapper and guarded invocation:

```sh
taskset -c 0,1 timeout 180 python3 /tmp/linear-eom-bounded.py lake env lean -j2 AUDIT_FILE
taskset -c 0,1 timeout 540 python3 /tmp/linear-eom-bounded.py lake build
```

The serialized full build passes 7787 jobs. All five retained scalar
diagnostics pass unchanged: one-dimensional counts, scalar Lorentz ranks,
actual finite-group controls, independent direct wave polynomials and all
cubature moments. These remain diagnostics rather than theorem premises.
The layout gate passes 2291 modules. Topic navigation passes all 163 topics
and outcomes; portable metadata, local links and whitespace checks pass.
Inherited module-system import advisories remain, with no proof, dependency
or audit-allowance change during integration.

## Cleanup and retained boundaries

Both local branch heads were confirmed reachable from master. No worktree
used either branch, and no remaining child branch required them. The local
`proof/scalar-quartic-four-completeness` and
`proof/derivative-literature-foundations` branches were safely retired with
`git branch -d`. Historical branch names remain in their topic records;
unrelated branches and worktrees were left untouched. The checkout remains
on master. No push, remote deletion or history rewrite occurred.

The final follow-up updates integration documentation only; no additional
Lean build is rerun after the merged-state proof gate above.

The [source register](references.md), successor source dictionaries and
[bibliography](../../proof/RELATED_LITERATURE.md) have been reconciled.
They retain pinned equation/table locations and distinguish comparisons
from proof premises. The [coverage ledger](../../verification/derivative-interface-coverage.md)
records the completed native scalar sectors and the remaining Higgs/Weyl,
physical-dictionary and full-paper boundaries. Dependency pins and published
input definitions are unchanged. No remote update is part of this request.
