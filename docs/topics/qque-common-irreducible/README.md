# Qque Common Irreducible Criterion

- ID: qque-common-irreducible
- Status: completed
- Result type: proved, including the full-field and actual-radical connections.
- Working branch: `proof/qque-common-irreducible`.
- Integration target: `master`.

## Frozen Endpoint

Add a common-irreducible-constituent criterion equivalent to the existing
nonzero Hom from Sym^2 Q to up-left tensor electron-left. Constituents are
compared AFTER taking these products, not pairwise between the three species.
Use actual multiplicities, not signed species indices.

Prove the algebraic common-simple-submodule criterion under source
semisimplicity. Derive symmetric-square semisimplicity from a finite-dimensional
compact continuous Q action, through the existing unitary model and tensor
square quotient. Connect to the complete coefficient classification and full
light-species/radical interfaces. Do not weaken old audits or dependency pins.

This is a representation-theoretic restatement useful with known decompositions,
not an executable group classifier or an unconditional existence theorem.
No full-spectrum, conjugation, virtual-index or pairwise-positivity assumption
is added. Existing arbitrary-H classification remains unchanged.

## Gates

Focused builds, strict transitive axiom audits, full build, layout/link/diff
checks, and relevant existing qque tests. Retain a regression showing that
post-product overlap need not be pairwise overlap before taking products.
LSP is unavailable; use source inspection and Lean builds.

## Result

- [CommonIrreducible](../../../Math/RepresentationTheory/Decomposition/CommonIrreducible.lean)
  defines overlap by isomorphic actual simple submodules over the group algebra.
  `nonzero_iff` proves equivalence with a nonzero intertwiner under source
  semisimplicity alone. The target need not be semisimple.
- [SymmetricSquareSemisimple](../../../Math/RepresentationTheory/Decomposition/SymmetricSquareSemisimple.lean)
  derives semisimplicity through the surjective tensor-square quotient. The
  compact adapter uses continuity only on the original finite-dimensional Q
  representation, and requires no supplied inner product or quotient topology.
- [QqueCommonIrreducible](../../../Physics/StandardModel/Operators/QqueCommonIrreducible.lean)
  proves `coefficient_iff`, `full_nonzero_iff`, and `radical_nonzero_iff` with
  the corresponding full-sector zero criterion. Full multiplicities are used,
  not a selected constituent. The radical adapter retains compact H and a
  compatible jointly continuous SM-cover x H action on the unchanged radical.
- The [Circle regression](../../../Physics/StandardModel/Operators/Audit/AuditQqueCommonIrreducible.lean)
  uses Q=1, up=z, electron=z^-1. It proves post-product overlap and a nonzero
  exterior coefficient, but no Q/up intertwiner or common constituent.
  This is an explicit field-model control, not a new ambient GUT source.

This supplies an equivalent constituent version of C, not equivalences of all
the old source packages with C. No index positivity is imposed. Old sufficient
conditions remain useful ways to guarantee the criterion, not necessary ones.
No remaining obligation for the frozen endpoint. Executable decomposition,
vacuum-derived H and operators outside the specified qque sector remain out
of scope. The existing arbitrary-H Hom classification is unchanged.

## Verification

All checks below passed at stage 01:

- `lake build Math.RepresentationTheory.Decomposition.CommonIrreducible Math.RepresentationTheory.Decomposition.SymmetricSquareSemisimple`
- `lake build Physics.StandardModel.Operators.QqueCommonIrreducible`
- `lake build Math.RepresentationTheory.Decomposition.Audit.AuditCommonIrreducible`:
  5 strict transitive axiom checks and no upper-layer imports.
- `lake build Physics.StandardModel.Operators.Audit.AuditQqueCommonIrreducible`:
  14 strict transitive axiom checks, including the Circle regression.
- Allowed axioms only: `propext`, `Classical.choice`, `Quot.sound`.
- `lake build`: 5766 jobs, success. Existing dependency/source linter warnings
  were replayed; the new modules produced no warnings.
- `python3 tools/qque/audit_one_generation.py`: 4 tests passed.
- `python3 tools/qque/audit_pairwise.py`: 3 tests passed.
- `python3 tools/qque/audit_contraction_uniqueness.py`: 3 tests passed.
- `node tools/layout/check-layout.mjs`: 715 modules, all checks passed.
- `node tools/docs/check-links.mjs`: no errors.
- `git diff --check`: passed.

Integration is recorded by Git ancestry of the retained topic branch into
`master`; no dependency pins, existing axiom policies or older proofs changed.

## Sources

- [Full light-species endpoint](../qque-full-species-boundary/README.md)
- [Semisimple module API](../../../Math/RepresentationTheory/Decomposition/SemisimpleSplitting.lean)
- [Symmetric-square descent](../../../Math/RepresentationTheory/SymmetricSquareDescent.lean)
- [Compact unitary model](../../../Math/RepresentationTheory/Decomposition/CompactIrreducibleQuotient.lean)
