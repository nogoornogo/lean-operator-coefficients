# Frozen Staged Plan

## Target And Hypotheses

One generation of the pinned minimal PS setup, with explicitly supplied field
branching and interactions. Complex couplings and high-scale VEV parameters;
selected heavy mass maps invertible on the eliminated sector. Original
higher-operator coefficients C_L,C_R and suppression scale are external inputs,
not conclusions. Scalar potential minimization and phenomenological fitting are
excluded. Fix normalization, conjugation and field ordering before proofs.

Target chain:

```
supplied PS contraction / Yukawa vertices
 -> high-scale VEV substitution and heavy-field elimination
 -> typed SM-invariant matter/Higgs coefficient (where applicable)
 -> specified EW VEV substitution and light-field projection
 -> derivative-free udd-neutrino coefficient and exact zero conditions.
```

The high-scale operator is dimension five in PS variables; the SM-invariant
completion and the LEFT four-fermion operator have different engineering
weights. Neither udd component notation nor a matching dimension count proves
a sector identification. Determine chirality, conjugation and B/L signs first.
Do not assume it is DUQL, QQQL, or qque. The common-copy/surplus qque theorem
is not a premise for this generation mechanism.

## Phase 1 — Convention Dictionary And Semantic Admission

Recover Eq.(19)'s epsilon contraction and Eqs.(10),(11)'s Yukawa sources.
Specify color, weak, Weyl indices, charge-conjugated fields, Hermitian conjugates,
Grassmann order, scalar normalization and each VEV. Identify Eq.(22)/(23)'s
LEFT operators and their B/L charges without relying on particle names.

Check two bounded routes: (A) an electroweak-covariant construction retaining
Higgs fields and eliminating the specified heavy neutral sector; (B) a direct
post-VEV construction with a separately justified light projection, compared
to the covariant coefficient by substitution. Route B alone is not proof of
SM-invariant dimension-seven admission. Inspect existing support factors and
actual-field interfaces; prove a candidate-to-sector map and evaluation identity.

Deliverable: convention table, source locations and exact proposed theorem
statements, including needed mass/projection conditions. Freeze the supported
L/R cases explicitly. Stop with the identified obstruction if a new all-sector
representation foundation or a different engineering sector is required; do
not insert a sector correspondence as an unchecked literature conclusion.

## Phase 2 — Reusable Symbolic Elimination And Substitution

Reuse paired quadratic elimination for the colored scalar where types and
normalization agree. Generalize only the minimal helper needed for unequal
sources/conjugate paired fields. Derive the on-shell cross coefficient from the
specified action with nonzero heavy mass, rather than supplying the desired
Wilson coefficient as a premise. Preserve signs, epsilon factors and 1/4 or
sqrt(2) conventions from the dictionary.

Construct reusable Higgs-VEV evaluation and field pullback/projection maps.
Prove equality on the independent exterior/symmetric coefficient sector, not
only commuting scalar polynomials. VEV invariance is under its stabilizer;
post-EW output must not be labelled invariant under the full unbroken SM.

Deliverable: shared algebraic helpers in Math/Physics and a bounded PS consumer
in GUT. Source ownership follows actual content; reusable Physics must not
import PS. No rate, propagation beyond the algebraic approximation, momentum
expansion or numerical diagonalization is involved.

## Phase 3 — Exact Light Projection And Generated Coefficient

A supplied linear projection can be an explicitly conditional interface, but
must not be advertised as derived from the actual mass. Provide an exact
one-generation mass-compatible control: the mu=0 neutral symmetric mass with
nonzero heavy mixing admits an explicit zero-mode vector. Fix normalization and
physical conjugation; avoid importing leading-order sin(theta) formulas as
exact identities. If finite mu is handled only with the paper's approximation,
state it as an external approximation and do not claim an exact arbitrary-mu
physical-light theorem. Exact finite-mu spectral diagonalization is not required.

Compose vertices, elimination and projection. Prove a generated-coefficient
equality in the fixed dictionary, and zero/nonzero iff conditions on the
specified parameter domain. Include zero UV coefficient, zero Yukawa/VEV or
projection, a nonzero exact point, and invalid zero-heavy-mass controls.
Separate L/R sectors; if their outputs share a sector, test combined cancellation
instead of concluding nonzero from one summand. Do not claim all allowed
coefficients are generated. Reconcile any normalization/sign discrepancy with
the paper before reporting agreement.

## Phase 4 — Apply The Completed Bridge To The Minimal PS Model

Instantiate the verified interfaces with the pinned one-generation PS field,
interaction, VEV and mass dictionary. List each admission hypothesis and whether
it is proved by the adapter or supplied from the literature. A generic
coefficient theorem alone does not complete this final model check.

Carry Eq.(19)'s contraction through the actual vertices and light projection.
Compare the resulting L/R coefficients with Eqs.(21)–(24), including field
order, normalization and the assumptions behind approximate mixing. Provide
an exact mass-compatible nonzero parameter control and zero/cancellation
controls within the supported domain. Verify that the surviving coefficient
belongs to the identified general sector and that its low-energy image is
nonzero on actual participating fields; an abstract allowed coefficient or a
nonzero scalar prefactor alone is insufficient.

Conclude explicitly which part of the paper's generation mechanism is verified,
under which conditions the selected Delta B=1 coefficient is generated or zero,
and which UV inputs or approximations remain external. Do not turn a zero in
one channel into a full proton-stability claim. If an earlier bounded phase
stops at an incompatibility, record its effect on this application as unverified;
do not claim the model check is complete.

Deliverables: a model-specific Lean application and strict audit for the
supported exact case, reproducible exact controls, a reader-facing result under
`docs/model-studies/pati-salam-protection/`, and an updated coverage row retaining
the pinned paper links. Exclude rates, numerical calculations and loop corrections.

## Acceptance And Stopping Conditions

- A typed bridge into the existing general completeness framework and its
  defined low-energy image, or an explicit scoped failure of that admission.
- A derived coefficient formula and actual mass-compatible light-projection
  control; all remaining supplied parameters/approximations enumerated.
- Final minimal-PS instantiation, comparison to the pinned equations, actual
  light-field nonzero/zero controls and explicit verified/unverified claims.
- Strict transitive axiom/import audits, focused builds, serialized full
  `lake build`, layout, exact reproducible controls, local links and diff check.
- Update the PS model study and literature coverage with precisely the checked
  equations and conditions; report partial certificates as partial.

No SO(10) proof is needed to accept the endpoint. Its literature supplies a
reuse motivation only. If a phase requires a new foundational or physical scope,
record the precise dependency and stop rather than reopening a new project.
Completion authorizes a verified topic commit, not a master merge.
