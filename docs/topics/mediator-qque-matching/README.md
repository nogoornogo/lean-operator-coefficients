# Mediator Exchange To Qque Coefficients

- ID: mediator-qque-matching
- Status: completed
- Result type: proved conditional construction and SU(5) reproduction.
- Working branch: `proof/mediator-qque-matching`.
- Integration target: `master`.

## Frozen Scope

Generalize the [SU(5) pilot](../su5-tree-matching/README.md), without changing
its bosonic or physical assumptions. Construct a paired mediator action with
an invertible linear mass operator, derive its stationary elimination, and
construct the ordered four-field coefficient from two linear current maps.
Use existing invariant-tensor and species-sector APIs to obtain an exterior
coefficient and, for the standard residual fields, its symmetric-square Hom
coordinate. Prove reconstruction and zero/nonzero equivalence, not universal
nonzero generation. Reproduce the SU(5) exchange as an application, retaining
its existing nonzero proof rather than supplying nonzero generation as input.

Inputs: mediator module and its dual, invertible mass map, coupling, linear
currents; equivariance or a proved invariance identity for the generated
tensor; existing field identifications and finite-dimensional hypotheses for
the Hom classification. No positivity, surjectivity or nonzero current is
silently added. Classification of an allowed space is not a proof that a
specific exchange element is nonzero.

Routes: direct dual evaluation and tensor regrouping; existing qque
alternation/sector/completeness. Stop if these require new representation or
QFT foundations. Do not derive a full UV Lagrangian, vacuum, propagator,
Grassmann reordering convention, or amplitude. No dependency changes.

## Source Interfaces

- [Scalar elimination](../../../Math/LinearAlgebra/PairedQuadraticElimination.lean)
- [Invariant evaluation](../../../Math/RepresentationTheory/InvariantPairing.lean)
- [Tensor regrouping](../../../Math/RepresentationTheory/OrderedInvariantPairing.lean)
- [Qque sector](../../../Physics/StandardModel/Operators/QqueCoefficientSector.lean)
- [Complete classification](../../../Physics/StandardModel/Operators/QqueCoefficientCompleteness.lean)
- [SU(5) application](../../../GUT/SU5/Matching/TreeMatching.lean)

## Acceptance

Focused and full builds, persistent strict transitive axiom audits, layout,
links and diff checks, existing exact qque regressions. Lean LSP unavailable;
use source inspection and targeted builds. Commit verified work and merge
with `--no-ff`; retain the branch and do not push.

## Results

### General Exchange

[MediatorExchange](../../../Math/LinearAlgebra/MediatorExchange.lean) works
over any field, with a mediator V, its algebraic dual, and a linear equivalence
`M : V equiv V`. M denotes the mass-squared operator in this paired quadratic
model, not the positive square root of such an operator. No common eigenvalue,
diagonal basis, positivity or finite-dimensionality is required for elimination.
The action is `y(Mx) + g (y(J) + K(x))`; its shifted identity and source equations
give `x = -g M^-1 J`, `y = -g K composed with M^-1`, and value `-g^2 K(M^-1 J)`.

Two linear current maps on the Q/U and Q/E tensors define a linear coefficient
on the ordered Q,Q,U,E tensor. `coefficient_eq_action` proves it is the
eliminated action, not a supplied Wilson coefficient. Further checks are:

- Exact zero criterion for nonzero g in terms of all pure-tensor source pairings.
- Invariance of the eliminated scalar under simultaneous mediator coordinate
  change, mass conjugation and dual-current transport.
- Scalar mass specialization, used by SU(5).
- A checked cancellation control: identity mass, g=1, nonzero J=(1,1) and
  K(x)=x_0-x_1 give zero exchange. These are source values, not a claim that
  every nonzero current map has identically zero exchange.

### Qque Connection

[MediatorQque](../../../Physics/StandardModel/Operators/MediatorQque.lean)
provides two ways to certify internal invariance: equivariant currents and
an equivariant invertible mass, or a proved invariance identity for the
constructed contraction. Neither takes a nonzero coefficient as input.
Existing spinor assembly and alternation then put this coefficient in the
independently defined species-degree (2,1,1) sector.

For the existing standard SM x H fields, with finite-dimensional up/electron
multiplicity carriers, `hom` gives its specific coordinate in
`Hom_H(Sym^2 V_Q, V_uc tensor V_ec)`. `reconstruct` returns exactly the generated
sector element, and `hom_eq_zero_iff` / `hom_ne_zero_iff` preserve its zero or
nonzero status. No new irreducible decomposition theorem or compactness
assumption is added. The arbitrary-field sector API is broader than this
standard-field Hom adapter; transporting concrete field identifications can
use the existing completeness API.

The Hom criterion concerns the descended sector element, not the unalternated
internal tensor. A nonzero ordered tensor alone is not claimed to survive
alternation. Classification of the allowed space does not establish that
the particular generated Hom element is nonzero.

### SU(5) Reproduction

[MediatorMatching](../../../GUT/SU5/Matching/MediatorMatching.lean) uses the
six-channel space, the original actual currents, and scalar mass operator
`25 g^2 v^2`. It proves:

- Its general exchange coefficient equals the original `orderedWilson * qque`.
- Invariance follows from that checked contraction identity; a separate
  representation of the six-channel space is not assumed or newly derived.
- The generated sector element equals the original exterior coefficient
  and is nonzero for nonzero real g,v.
- Its ordered spinor tensor equals the original six-channel eliminated action.

No premise of the old SU(5) theorem was strengthened or removed. This example
checks the general sector construction; it does not separately compute a
one-generation residual Hom coordinate for SU(5).

### Boundary And Stop

The approved endpoint is closed. These results supply a reusable exchange
construction, not universal nonzero generation for SU(N), Spin or E6. Each
further application must derive currents, appropriate mass data and invariance,
then establish nonzero descent without hiding cancellation in a hypothesis.
The previous pilot's UV-action, vacuum, normalization, Grassmann-ordering,
energy-hierarchy and amplitude boundaries remain unchanged.

### Verification

- Focused build of the three new audit modules passed: 11 Math, 8 Physics,
  7 SU(5) strict transitive checks. Only `propext`, `Classical.choice` and
  `Quot.sound` are permitted. No new axioms, `sorry`, limits or dependency pins.
- Full `lake build`: passed, 5785 jobs. Existing warnings were replayed;
  new proof files had no warnings. Repeat the build on the merged state.
- Layout check: 734 modules; aggregate registration and layer checks passed.
- Exact qque regressions: `python3 tools/qque/audit_one_generation.py` (4),
  `python3 tools/qque/audit_pairwise.py` (3),
  `python3 tools/qque/audit_contraction_uniqueness.py` (3) all passed.
  These check existing finite conventions, not a general physical UV model.
- Local links and `git diff --check` are checked before and after integration.
- Git ancestry records the topic and merge commits. Retain the branch;
  no remote push is authorized.
