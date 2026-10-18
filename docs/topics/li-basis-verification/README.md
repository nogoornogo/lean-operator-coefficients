# Li Basis Verification Pilot

- ID: `li-basis-verification`
- Status: completed
- Result type: proved (explicit normalized local D.38 interpretation)
- Working branch: `proof/li-basis-verification`
- Integration target: `master`
- Integration evidence: Git ancestry into the recorded target; report merge outcome

## Endpoint And Scope

This topic tests whether a finite operator basis produced by the framework of
Li--Ren--Xiao--Yu--Zheng can be checked against an operator sector already
proved complete in this repository.  The pilot sector is the derivative-free,
dimension-six `qque` field type.  It is chosen because its gauge/Lorentz
contraction and its repeated-`Q` statistics are already connected to the
residual coefficient space

```text
Hom_H (Sym^2 Q, U tensor E).
```

The intended result is an explicit linear equivalence, not agreement of a
dimension count.  Each literature candidate must first be represented as an
element of the existing Lean coefficient sector.  Its coordinates in the
proved `qque` presentation must then be computed, and an explicit inverse (or
equivalent independence and spanning proofs) must be checked in Lean.

The residual group and multiplicity representations remain explicit inputs.
The pilot does not claim to formalize the full paper, the complete ABC4EFT
package, all SMEFT dimensions, derivatives, EOM/IBP reduction, amplitudes, the
`m`-basis or the `j`-basis.  A broader endpoint requires a separate scope
decision after this certificate path is demonstrated on one field type.

## Deliverables And Acceptance

1. Record the exact dictionary between the paper/package field convention and
   this repository's signed-field, chirality and dual-space convention.
2. Encode the selected external candidate contractions as Lean maps into the
   existing `qque` coefficient sector.  Imported labels or coefficient arrays
   are data, not trusted completeness theorems.
3. Reuse the proved `qque` completeness equivalence to obtain canonical
   coordinates, including the repeated-`Q` symmetry.
4. Check an explicit two-sided coordinate inverse, or prove the equivalent
   linear-independence and spanning statements.
5. Persist a strict audit showing that the final theorem has no custom axioms
   and depends only on the intended source layers.

The pilot is accepted only when both the semantic bridge (candidate operator to
the existing coefficient sector) and the finite linear certificate are proved.
A rank computation detached from that bridge is insufficient.

The investigation stops for a scope decision if the precise external output is
not publicly recoverable, its convention cannot be matched without adding the
deferred EOM/IBP or amplitude foundations, or the claimed `qque` object belongs
to a different conjugation/chirality sector.

## Implemented Result And Boundaries

The [source-recovery investigation](source-recovery.md) recovered PDF appendix
D.1 equation (D.38). The [frozen implementation contract](implementation-contract.md)
and [proof dossier](../../proof/current/applications/Physics/LI_QQUE_BASIS.md) specify its normalized
local contraction interpretation.

- Constructed gauge bidual equivalences identify the daggered singlets with
  repository right-Weyl fields and residual dual actions. Actual physical
  conjugate-field identifications remain explicit model obligations.
- The printed `Q,Q,E,U` contraction, including all epsilon and spinor factors,
  agrees with repository `Q,Q,U,E` after the Fermi sign. Raw alternatization's
  factor 2 is explicit, and the candidate lands in the independent sector.
- Finite coordinates on `Hom_H(Sym² A,B tensor D)` use unordered Q pairs and
  U,E tensor-basis rows. Matrix intertwining equations retain arbitrary H.
- Both coordinate inverse identities are proved. With trivial residual action,
  matrix-unit candidates form an independent spanning family; their pure-tensor
  evaluation is exactly the normalized printed contraction. Three equal flavor
  spaces of size 3 give 54 candidates.

This checks the printed candidate under the explicit local dictionary.
ABC4EFT runtime output, general amplitude correspondence, physical external-state
normalization, derivatives and EOM/IBP remain outside the result.

## Verification

- Focused build: `lake build Physics.StandardModel.Operators.Audit.AuditLiQqueBasis`: 3303 jobs passed.
- Strict transitive audit: `lake env lean Physics/StandardModel/Operators/Audit/AuditLiQqueBasis.lean`: 34 checks passed.
- Existing qque audit: `lake env lean Physics/StandardModel/Operators/Audit/AuditQqueCoefficientAssembly.lean`: 41 checks passed.
- Full build: `lake build`: 6379 jobs passed, exit 0; no warnings in final build output.
- Layout: `node tools/layout/check-layout.mjs`: 1052 modules passed.
- Markdown links: `node tools/docs/check-links.mjs`: zero errors.
- `git diff --check`: passed.
- Exact component checks: `audit_li_d38.py` (3 tests), `audit_one_generation.py`
  (4 tests), `audit_pairwise.py` (3 tests), all passed; see
  [the test dictionary and finite scope](../../../tools/qque/README.md).

An initial full build was interrupted by concurrent rebuilding of a changed
shared dependency: two consumers reported a missing `QqueResidualHom.olean`.
This is not recorded as a passing build. The successful final full build ran after source edits and focused builds
finished, without another concurrent Lake build.

All five acceptance deliverables are closed for the explicit normalized local
interpretation, as detailed in the proof dossier. Initial source-recovery
checkpoints are `checkpoint 01` and its PDF correction `checkpoint 02`. The verified endpoint
is committed as `checkpoint 03` on the historical branch `proof/li-basis-verification`.
The user explicitly authorized integration into `master` at stage 01.
Git ancestry into the recorded target is authoritative for integration;
the merge outcome and merged-state verification are reported with integration.

Integrated into `master` with merge commit `checkpoint 04` at stage 01.
Merged-state verification repeated the full build (6379 jobs), both strict
audits (34 and 41 checks), layout (1052 modules), Markdown links (zero errors),
all 10 exact component tests and `git diff --check`; all passed. The link
checker required a sandbox retry permitting its read-only Git subprocess.

## References

- [Li et al., *Operators For Generic Effective Field Theory at any Dimension*,
  JHEP 04 (2022) 140](https://arxiv.org/html/2201.04639v2)
- [Common operator completeness interface](../operator-completeness-interface/README.md)
- [Qque coefficient completeness](../qque-coefficient-completeness/README.md)
- [`QqueCoefficientCompleteness`](../../../Physics/StandardModel/Operators/QqueCoefficientCompleteness.lean)
- [`QquePhysicalExteriorCompleteness`](../../../Physics/StandardModel/Operators/QquePhysicalExteriorCompleteness.lean)
