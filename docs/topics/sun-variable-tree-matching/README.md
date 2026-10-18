# Variable Diagonal Exterior Matching

- ID: sun-variable-tree-matching
- Status: completed
- Result type: proved conditional uniform matching.
- Working branch: `proof/sun-variable-tree-matching`.
- Integration target: `master`.

## Frozen Endpoint

The user authorizes starting directly with variable diagonal backgrounds,
with fallback to the fixed-background family if needed. On exterior-square
matter of the defining SU(5+r) matrix action, retain the first-five-coordinate
ten and its existing Q/up/e fields. Supply a real diagonal background with
first three entries a, next two b, arbitrary remaining entries, trace zero,
a != b, and nonzero real g. Keep the checked paired quadratic action.

Derive the currents from the exterior action, enumerate all unequal-weight
root pairs exactly once, and invert mass only on that sector. Prove equality
to the SU(5) exchange at effective v=(a-b)/5, hence nonzero intrinsic qque
sector and ordered scalar -1/(a-b)^2. Derive additional-current zero, including
extra-to-extra roots; do not assume support, mass equality or nonzero exchange.
Check SU(5)/SU(6) recovery and SU(7) equal/unequal spectator weights.

Routes: exterior compression for actual currents; diagonal mass algebra and
generic inheritance for matching. Stop or use the authorized fixed-background
fallback if new representation/topological/QFT foundations are required.
No full vacuum, light mass radical, anomaly-free matter completion, general
mixing, arbitrary group embedding, amplitude or decay width is claimed.

## Source Interfaces

- [Plan](../post-su6-generalization/README.md)
- [SU(6) currents](../../../GUT/SU6/Matching/ExteriorCurrents.lean)
- [SU(6) assembly](../../../GUT/SU6/Matching/TreeMatching.lean)
- [Exterior compression](../../../Math/RepresentationTheory/ExteriorSquareCompression.lean)
- [Diagonal mass](../../../Math/LinearAlgebra/DiagonalAdjointMass.lean)
- [SU(5) matching](../../../GUT/SU5/Matching/MediatorMatching.lean)
- [Inheritance](../../../Math/LinearAlgebra/MediatorInheritance.lean)

## Acceptance

Focused and full builds, strict persistent transitive axiom audits, exact qque
regressions, layout/link/diff checks, commit and no-ff merge into master,
merged-state checks, retain branch, no push. No sorry, new axioms, dependency
or heartbeat changes. Lean LSP is unavailable; use targeted builds.

## Results

The variable-background route succeeds; the authorized fallback is not needed.
For every natural r, real diagonal background in the frozen class and nonzero
real g, the generated intrinsic qque sector is nonzero. Additional weights
may coincide with each other or with a,b. No nonzero full exchange, zero
additional currents or full-matrix invertibility is assumed.

### Derived Construction

- [Exterior block](../../../Math/RepresentationTheory/ExteriorSquareBlock.lean)
  constructs the split five-coordinate inclusion and derives compression
  of the actual infinitesimal exterior action for arbitrary added dimension.
- [Exterior matter](../../../GUT/SUN/Matching/ExteriorMatter.lean) constructs
  the defining SU(5+r) representation and its exterior square, an injective
  SU(5) block homomorphism, and the retained-action intertwining identity.
  The Q embedding is covariant under the existing full SM covering-group action.
- [Background](../../../GUT/SUN/Matching/DiagonalBackground.lean) records the
  real entries, color/weak block values, trace zero and a != b. The supplied
  background is proved Hermitian and traceless. Channels are the six core
  pairs plus ordered unequal-weight pairs with an extra coordinate.
  Coverage and injectivity prove no missing or duplicated broken root pairs.
- [Currents](../../../GUT/SUN/Matching/ExteriorCurrents.lean) computes both
  projected currents from matrix-root actions. Core currents equal the
  checked SU(5) ones; every additional current vanishes, including massive
  extra-to-extra roots.
- [Matching](../../../GUT/SUN/Matching/TreeMatching.lean) constructs the
  invertible mass only on these channels. Its coordinate values agree with
  the proved double-commutator eigenvalues g^2(d_i-d_j)^2 in both orientations.
  Equal-weight directions have zero mass entries and are not integrated out.

### Endpoint

The retained mass is exactly the SU(5) mass at effective v=(a-b)/5.
`coefficient_eq` proves equality of the full ordered coefficient with the
SU(5) coefficient at that value. `generated_eq` proves equality of the
intrinsic exterior sector; `generated_nonzero` then reuses the existing
nonzero exterior theorem. This is stronger than assuming an ordered
nonzero functional survives alternation.

`wilson_value` and `full_action_eq` identify the eliminated paired action
with the ordered qque functional times -1/(a-b)^2, in the existing convention.
The trace-zero condition is a physical-background admissibility input, not
the source of the exchange nonzero proof; the essential core gap is a != b.

### Specializations

[Controls](../../../GUT/SUN/Matching/Controls.lean) proves:

- The fixed background v diag(2,2,2,-3,-3,0,...,0) has exactly the old SU(5)
  coefficient and generated sector for every r, recovering the first-stage
  family as a specialization rather than a separate implementation.
- r=0 recovers the SU(5) coefficient. r=1 recovers the actual SU(6) matter embedding,
  projection, background, coefficient and generated sector; an explicit
  bijection identifies its five additional channels, currents and masses.
- The SU(7) family diag(2,2,2,-3,-3,t,-t) has the same generated sector for
  every real t. At t=0 the additional pair is massless; at t=1 it is massive
  with mass squared 4g^2 and both projected currents zero; t=2 tests a
  spectator eigenvalue coinciding with the color block. Nonzero descent
  holds throughout without a global nondegeneracy premise.

### Boundary

This is a conditional theorem for a uniform matrix-group/exterior-matter
family, not all SU(N) representations or embeddings. The retained ten is
chosen, not derived as a fermion mass radical. Background selection,
kinetic/action normalization, anomaly cancellation, full UV interactions,
arbitrary mass mixing, loop effects, physical amplitudes and widths remain
outside the endpoint. No claim of a uniform low-energy approximation near
a vanishing spectator mass is made by these exact algebraic equalities.
The representation-separated sufficient criterion is not instantiated here;
support follows directly from the exterior action.

## Verification

- Focused controls build passed. Strict audits are registered in
  [Math](../../../Math/RepresentationTheory/Audit/AuditExteriorSquareBlock.lean)
  and [GUT](../../../GUT/SUN/Audit/AuditVariableMatching.lean), allowing only
  `propext`, `Classical.choice`, `Quot.sound`.
- Exact existing regressions passed: `python3 tools/qque/audit_one_generation.py`
  (4 tests), `python3 tools/qque/audit_pairwise.py` (3), and
  `python3 tools/qque/audit_contraction_uniqueness.py` (3).
  New family and degeneracy controls are Lean proofs, not numeric samples.
- `node tools/layout/check-layout.mjs`: passed, 760 modules.
- Full `lake build`: passed, 5811 jobs. Both persistent audits pass:
  7 Math and 63 GUT declarations, 70 strict transitive checks in total.
  Existing warnings were replayed; new proof files have no warnings.
- `node tools/docs/check-links.mjs`: passed, 292 Markdown files,
  1736 local inline links, 33 heading fragments.
- `git diff --check`: passed.
- No existing proof, dependency pin, heartbeat or axiom policy changed.
  Repeat full build, regressions and layout/link/diff checks after integration.
  Git ancestry records topic/merge commits; retain branch and do not push.

The frozen endpoint is complete. No fallback was used and no additional
model investigation is needed for this family theorem. Other representations,
non-diagonal/mixed mass models and physical amplitudes are separate tasks.

The subsequent [compatible transport result](../sun-conjugate-matching/README.md)
handles simultaneous unitary conjugation of this background and retained
fields, plus mediator-coordinate changes. Independent mass mixing remains open.
