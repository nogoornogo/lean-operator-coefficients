# Follow-Up Plan: Model Admission And Normalized Light Fields

- Status: completed with a bounded convention stop; see [result](follow-up-result.md)
- Record and working branch: continuation of `ps-bnv-coefficient-bridge` on
  `proof/ps-bnv-coefficient-bridge`; no new top-level branch or master integration
- Existing conditional certificate: `checkpoint 01`
- The original [frozen plan](plan.md) and its bounded stop remain historical
  evidence for that certificate; this document defines the proposed next scope.

## Purpose And Frozen Target

Close selected model-input gaps in the [conditional PS result](result.md), while
producing reusable normalization and coefficient-pullback lemmas. The endpoint
is an exact one-generation, mu=0 application for a specified Higgs direction,
not a verification of the entire paper or a proton lifetime calculation.

Target chain:

```
explicit PS tensors and chosen VEVs
 -> derived participating SM components and neutral mass entries
 -> exact mass-kernel injection with unit kinetic normalization
 -> existing generated exterior coefficient on those light fields
 -> nonzero criterion and separately qualified paper comparison.
```

Retain complex parameters, nonzero eliminated masses, and external UV
coefficients C_L,C_R. Canonical positive Hermitian kinetic forms are explicit
inputs: proving their normalization consequences does not derive the full
kinetic action. Choose mu=0 exactly. Do not substitute the paper's finite-mu
approximation for an exact mass-kernel theorem. Specify the selected Phi/Higgs
embedding and VEV; their vacuum selection is an input, not a consequence of a
scalar potential. A selected-VEV component identity must not be described as
a full PS branching/stabilizer theorem.

## Phase 1 — Freeze The Source Dictionary Before Coding

Use [2211.02054v2](https://arxiv.org/abs/2211.02054v2),
[PDF](https://arxiv.org/pdf/2211.02054v2), Eqs.(1),(2),(6),(10)–(14),(19)–(24).
Tabulate representations, index order, conjugation, mass-action factor 1/2,
kinetic forms, vR versus component VEV, and scalar versus exterior coefficients.
Derive the neutral mass entries directly from the same component action used
for the colored-scalar vertex; do not define M by the desired output formula.

Inspect at most two routes: direct two-component translation of this source;
and a convention cross-check against its cited predecessor
[2012.05976v2](https://arxiv.org/abs/2012.05976v2),
[PDF](https://arxiv.org/pdf/2012.05976v2), Eqs.(2.10),(2.15),(2.17).
The predecessor's VEV definition must not be transferred unchanged.

Deliverable: explicit dictionary and proposed theorem signatures. If the
displayed equations cannot be reconciled, distinguish a consistent component
action certificate from agreement with every displayed paper formula. Record
the unresolved convention; do not label the paper erroneous or silently
choose a coupling redefinition. This can stop the full-prefactor comparison
without invalidating an independently specified model-action calculation.

## Phase 2 — Reusable Normalization And Nonzero Transport

First freeze the minimal interfaces supported by existing sources. For a
nonzero exact zero mode z in a finite-dimensional complex inner-product space,
construct z / norm(z), prove unit norm and continued mass-kernel membership.
For the one-dimensional light line, prove the coefficient pullback transforms
by the appropriate scalar or conjugate scalar in its signed field slots.
Deduce preservation of nonzero under nonzero normalization.

Prove a more general basis-change statement only if it follows directly from
the existing alternating-map interfaces: invertible changes of coordinates
inside the same light space preserve zero/nonzero. Arbitrary injective maps
into a larger field space do not guarantee nonzero restriction. Do not expand
this phase into a general spectral/Takagi decomposition project.

Use Math for pure inner-product/multilinear lemmas and Physics for signed-field
adapters where needed. Neither may import PS. Instantiate the existing exact
kernel (1,0,-d/M) in GUT, including the barred xi projection and complex phases.
Deliverable: reusable lemmas plus the normalized mu=0 PS light injection.

## Phase 3 — Bounded PS Component Adapter

Represent only the participating finite PS tensor spaces, index contractions
and explicit SM component embeddings needed by the source action. Prove the
selected restrictions of chi, fL, fR and Phi give the component vertices and
Dirac mass used in the certificate. Preserve the two Higgs directions in the
dictionary; choosing one direction does not prove the other decouples.

Derive the relation among neutral mixing M, Yukawa vertex y and the high-scale
VEV from the fixed action. Verify Eq.(19)'s restrictions, color/weak epsilon
factors, conjugation and field order against the existing UVComponent and
TypedVertex certificates. Check participating SM charges explicitly.

No full PS group/quotient/stabilizer infrastructure, all-representation
branching, vacuum minimization or all-channel operator classification is
required. If an indispensable missing interface needs such a foundation,
record its exact statement and stop for a scope decision.

## Phase 4 — Compose And Compare

Compose the derived component adapter, existing stationary-field elimination
and normalized light injection. Prove equality of actual exterior coefficients,
not only equality of scalar prefactors. State exact zero/nonzero conditions
on the admitted parameter domain, retaining C_L,C_R as UV inputs.

Compare separately:

1. existence of a nonzero generated coefficient in the exact mu=0 model;
2. its canonically normalized prefactor in the fixed dictionary;
3. agreement with the paper's displayed prefactor and normalized mixing angle.

Do not infer (3) from (1), or a finite-mu theorem from mu=0. Include complex
phase, zero UV/Yukawa/VEV, nonzero exact-point and invalid heavy-mass controls.
Retain independent LR/RR tensor probes; this does not exclude interference in
hadronic amplitudes. Exclude rates, loops, RGE, numerical diagonalization,
hadronic matrix elements and ultraviolet generation of C_X.

## Acceptance, Stops And Reporting

Accept a scoped normalized-model certificate only when every input is marked
derived, supplied, or unresolved and the actual light coefficient is proved.
Accept the complete paper-prefactor comparison only if its convention and
normalization correspondence is separately proved. A precise feasibility stop
or mismatch is valid and must not be presented as paper-wide verification.

For proof changes: focused builds, persisted strict transitive axiom/import
audits, one serialized full lake build, layout check, relevant exact scripts,
local links and diff check. Keep pins and audit policies unchanged. For planning
alone: links and diff check; no new Lean verification baseline.

Update the topic result, the [PS model study](../../model-studies/pati-salam-protection/generated-coefficient.md)
and the [coverage ledger](../../verification/proton-protection-model-coverage.md)
only at verified milestones, with pinned equation links and explicit boundaries.
Commit coherent verified milestones on the existing branch; master merge
requires separate user direction.

Implementation reached the convention stop after reusable normalization and
finite component checks. No further proof work is active; see the result for
verified and unresolved obligations.
