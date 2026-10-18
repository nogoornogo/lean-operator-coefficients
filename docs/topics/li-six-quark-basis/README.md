# Literature Basis Verification For The Specified Six-Quark Sector

- ID: `li-six-quark-basis`
- Status: completed
- Result type: extended local orbit basis and constrained residual-Hom certificate
- Working branch: `proof/li-six-quark-basis`
- Integration target: `master`
- Integration evidence: Git ancestry against `master`; merge explicitly authorized at stage 01

## Endpoint And Scope

The approved arbitrary-multiplicity extension is verified. Twenty-five
selected literal orbit contractions from Li's ten recovered Young seeds plus
one separately identified alternating-down / symmetric-up seed form a basis
of the independent local color/Weyl invariant space. The first ten seed orbits
cannot span the added component, by a Lean-checked separating probe.

The coordinate equivalence transports all four typed exchange equations and
residual H-equivariance, with both physical-sector inverse identities and
actual-field transport under the existing `Inputs`. Up/down carriers remain
distinct and finite-dimensional; no dimension-at-most-three hypothesis is added.
The 25 local coordinates are not 25 free flavor maps.

## Results And Boundaries

- [Completed proof dossier](../../proof/current/applications/Physics/LI_SIX_QUARK_BASIS.md).
- [Results and verification](results.md).
- [Source dictionary and citation limits](source-recovery.md).
- [Approved plan and stop gates](plan.md).
- [Exploratory rank checkpoint](rank-investigation.md).
- [Cross-topic literature verification coverage](../../verification/li-basis-coverage.md).
- [Completed child: exact printed-span and flavor boundary](../li-six-quark-flavor-boundary/README.md).

Scalar flavors recover the established two probes and dimension two. The added
component fails scalar statistics, but a determinant flavor tensor with up
carrier C and down carrier C^4 gives a nonzero physical exterior coefficient.

The result is an extension of the printed list in the specified epsilon
interpretation. It is not a paper-wide error claim, an eleven-factor Schur
decomposition, general flavor counting, or all dimension-nine SMEFT completeness.
Primitive-coordinate normalization is explicit; four-component C-matrix and
hook-length-normalization agreement are not claimed. No new physical matching,
derivative, EOM/IBP, amplitude or general p/y/m/j endpoint is included.

## Verification

On stage 01:

- Focused audit build: 3,295 jobs, 18 strict transitive axiom checks passed.
- Full `lake build`: 6,412 jobs, successful.
- `python3 tools/li-six-quark-check.py`: exact rank and two-sided inverse assertions passed.
- Layout: 1,085 modules; layer, import, cycle, aggregate and relocation checks passed.
- Local Markdown links and `git diff --check`: passed.

No Lean/dependency pin changes or audit exceptions were introduced. The
persistent audit permits only `propext`, `Classical.choice` and `Quot.sound`.
The user subsequently authorized master integration at stage 01. Git ancestry
records integration; the final flavor-boundary verification is in the linked child topic.

## References

- [Existing physical/actual-field classification](../delta-b-two-model-interface/README.md)
- [Precise constrained Hom boundary](../delta-b-two-model-interface/flavor-hom.md)
- [Existing conventional basis and normalization](../delta-b-two-conventional-basis/README.md)
- [Li et al., dimension-nine SMEFT](https://arxiv.org/abs/2007.07899)
- [Li et al., generic EFT construction](https://arxiv.org/abs/2201.04639)

The papers supply candidate expressions and motivation, not trusted completeness premises.
