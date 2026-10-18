# CLFV Dipole Coefficient Completeness

- ID: `clfv-dipole-completeness`
- Status: completed
- Checkpoint detail: completed (bounded algebraic endpoint); merged
- Integration result: [merge chain and verification](integration.md), master merge `checkpoint 01`.
- Result type: proved
- Working branch: `proof/clfv-dipole-completeness`
- Integration target: `master`
- Integration policy: per the user's stage 01 instruction, no milestone
  merges before the overall goal is achieved or work is interrupted. Retain
  verified milestone commits on this branch. No remote push is authorized.

## Endpoint And Scope

Classify the independently specified dimension-six charged-lepton dipole
coefficient sectors with one lepton, one charged singlet, one Higgs and one
field strength, for the B and W gauge channels. Prove an equivalence with
residual intertwiners, then classify a prescribed flavor component and its
realization by a coefficient-generation map on an arbitrary input domain.
Do not assume that this generation map is linear or surjective.

Use the existing algebraic SM covering product and SL(2,C) Weyl conventions.
The all-left conjugate convention uses L, Ec, conjugate Higgs, and the
appropriate chiral field strength. Record all duals and normalizations in
the statement dossier before connecting this convention to the operators.
The Higgs has one residual-trivial copy at the initial endpoint; additional
Higgs multiplicities must be stated explicitly in any extension.

Neither Wilson-coefficient matching calculations, RGE, a derived mass basis,
decay rates nor experimental limits are part of the endpoint. Flavor labels
are supplied identifications. An allowed coefficient is not a proof that a
UV model generates it. Concrete examples are controls, not model restrictions.

## Deliverables And Acceptance

1. General normalized-contraction extraction and reconstruction, independent
   of operator species. No image-defined sector may replace completeness.
2. Explicit local gauge and chiral spinor representations, contractions and
   exhaustive uniqueness for both dipole channels.
3. Independent ordered multilinear sectors and residual Hom equivalences;
   state the distinct-fermion convention and actual-field transport.
4. Flavor selection and arbitrary-domain generation: classify vanishing and
   nonvanishing inputs and separate allowed from realized coefficients.
   Linear/affine kernel statements are optional specializations.
5. Persistent strict transitive axiom/import audits, focused and full builds,
   layout/link checks, statement review and verified milestone commits.

No custom axioms, `sorry`, dependency changes or assumed local uniqueness
may be used to declare the physical completeness endpoint proved. A theorem
parameter describing local uniqueness remains an open physical obligation
until discharged. New foundational scope or a counterexample affecting the
agreed endpoint requires a recorded decision.

## Work And Open Obligations

All five deliverables are closed for the stated chiral, single-Higgs endpoint.
The complete ordered SM sectors are equivalent to two residual Hom spaces;
local uniqueness is proved, not assumed. Prescribed flavor selection and
arbitrary-domain generation have exact criteria and explicit sufficient and
forbidden-input interfaces. See [results](results.md) for the theorem map.

Model-specific matching, deriving flavor identifications and concrete UV
input conditions remain beyond this endpoint. The nonlinear two-flavor
control is a sample, not a restriction of the classification. A comparison
with qque's model hypotheses can now use the proved Hom interfaces.
No milestone or completion merge has been performed.

The bounded [input-structure child](../clfv-dipole-input-structure/README.md)
extends the generation interface to finite mediator paths and nonlinear
weights. Its results and branch remain separate and unmerged.

## Result And Verification

- Planning commit: `checkpoint 02`.
- Proof commit: `checkpoint 03`.
- Focused dipole audit: passed, 3548 jobs and 50 strict transitive axiom checks.
- Full `lake build`: passed, 5905 jobs; existing dependency warnings replayed,
  no new-source warnings in the final focused build.
- Layout: 854 modules, passed. Local links and `git diff --check`: passed;
  final documentation counts are recorded in [results](results.md).
- Lean LSP MCP was unavailable; source inspection and CLI builds supplied
  diagnostics. Lean/dependency pins and axiom allowlists are unchanged.
- The final result-record update is documentation-only; no Lean build is
  rerun for that update. The proof baseline is the build of `checkpoint 03`.

## References

- [Qque completeness](../qque-coefficient-completeness/README.md)
- [External invariant factorization](../../../Math/RepresentationTheory/ExternalInvariantFactorization.lean)
- [Invariant tensor currying](../../../Math/RepresentationTheory/InvariantTensorCurry.lean)
- [Weyl spinors](../../../Physics/FieldTheory/Spinor/WeylSpinor.lean)
- [SM gauge fields](../../../Physics/StandardModel/Gauge/StandardSMGaugeTensor.lean)
- [Statement dossier](statement.md)
- [Proof results and verification](results.md)
- [Linear protection classification](../yukawa-protection-kernel/README.md)
- [Warsaw basis, Grzadkowski et al.](https://arxiv.org/abs/1008.4884)
- [One-loop seesaw dipoles, Zhang and Zhou](https://arxiv.org/abs/2102.04954)
