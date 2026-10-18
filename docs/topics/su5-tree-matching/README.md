# SU(5) Adjoint Mass And Tree Matching Pilot

- ID: su5-tree-matching
- Status: completed
- Result type: conditional algebraic tree matching, with a proved nonzero exterior descent.
- Working branch: `proof/su5-tree-matching`.
- Integration target: `master`.

## Frozen Endpoint

Continue the [current-block pilot](../su5-current-blocks/README.md) with an
explicit additional bosonic model: real gauge coupling g and adjoint background
`D = v diag(2,2,2,-3,-3)`. Assume g and v nonzero for the massive endpoint.
These are model inputs, not consequences of the selection-rule theorem.
Derive the cross-block mass eigenvalue from `g^2 ad_D^2`, in a stated
normalization. No Higgs potential, vacuum selection or numerical scale is
inferred; positive mass is not a proved hierarchy of energies.

Prove a reusable exact elimination identity for a paired quadratic mediator
action. Construct both currents from the actual exterior-square action, sum
the six color/weak exchange channels, and compare the derivative-free
ordered internal coefficient with the existing qque contraction. Where the
existing spinor/exterior API suffices, retain a checked nonzero descent.
Keep the distinction between a local algebraic tree matching model and an
interacting quantum field theory explicit.

## Inputs, Routes And Stop Gate

Inputs beyond the retained fermion representation: the specified adjoint
background, a common gauge coupling, and a normalized paired heavy-field
quadratic action. Nonzero currents, a nonzero qque projection and a nonzero
matching coefficient must be derived, not assumed.

Use two bounded routes: (1) diagonal commutator masses plus bilinear square
completion; (2) explicit current contractions via exterior polarization and
the existing complete qque tensor. Stop and record a scoped feasibility
boundary if physical matching needs additional foundational machinery.
Do not replace a missing matching bridge by defining it to equal qque.

Derivative corrections, momentum-dependent propagators, gauge fixing, loop
matching, arbitrary Higgs vacua, arbitrary GUT matter, hadronic amplitudes
and decay rates are outside this pilot. Dependency pins remain unchanged.

## Acceptance

Focused builds, persistent strict transitive axiom audits, full `lake build`,
layout and link checks, and relevant exact qque regression scripts for new
contraction/sign bridges. Lean LSP is unavailable; use source and builds.

## Sources

- [Actual currents](../../../GUT/SU5/Representations/CurrentBlocks.lean)
- [Exterior coordinates](../../../Math/RepresentationTheory/ExteriorSquareCoordinates.lean)
- [SM gauge contraction](../../../Physics/StandardModel/Gauge/StandardSMGaugeTensor.lean)
- [Spinor and exterior endpoint](../../../Physics/StandardModel/Operators/QqueSpinorExterior.lean)
- [Classical tree matching reference](https://arxiv.org/abs/1711.10391)

## Results And Verification

### Proved Chain

1. [Diagonal mass algebra](../../../Math/LinearAlgebra/DiagonalAdjointMass.lean):
   for any finite index type and commutative ring, the double commutator acts
   on the ij entry by `(d_i - d_j)^2`.
2. [SU(5) mass model](../../../GUT/SU5/Matching/AdjointMass.lean):
   the supplied background is traceless and Hermitian. Each upper and lower
   color/weak matrix unit has mass eigenvalue `M^2 = 25 g^2 v^2 > 0` for
   real nonzero g,v. Vanishing g or v is a checked degenerate control.
3. [Actual currents](../../../GUT/SU5/Matching/HeavyCurrents.lean):
   exterior-square infinitesimal action, projected through the existing
   matter branching, gives Q -> up-dual and Q -> electron-dual currents.
   They use opposite complex root directions, not two arbitrarily selected
   nonzero entries. Summing all six pairs gives exactly the existing qque
   internal tensor, with no assumed nonzero current or no-cancellation premise.
4. [Generic elimination](../../../Math/LinearAlgebra/PairedQuadraticElimination.lean):
   for any field and bilinear pairing B, the action
   `m B(x,y) + g (B(J,y) + B(x,K))` at
   `x = -g/m J`, `y = -g/m K` equals `-g^2/m B(J,K)` when m is nonzero.
   The source equation and absence of a linear variation term are proved.
   This is algebraic stationarity, not a path-integral or kinematic on-shell claim.
5. [Spinor-vector pairing](../../../Physics/FieldTheory/Matching/PairedVector.lean):
   an explicit nondegenerate complexified vector pairing satisfies
   `B(s tensor z, t tensor l) = eps(s,t) eps(z,l)`.
6. [Matching](../../../GUT/SU5/Matching/TreeMatching.lean):
   `eliminated` is defined by evaluating and summing the quadratic actions,
   not by prescribing a qque coefficient. `eliminated_eq` identifies it with
   `c * qque * eps * eps`, where `c = -g^2/M^2 = -1/(25 v^2) != 0`.
   `matchedOrdered_eq_eliminated` connects this result to the existing
   invariant-tensor API. A basis probe of its exterior descent is `2c`,
   proving the descended coefficient is nonzero.

The reusable deliverables are the dimension-independent diagonal mass lemma,
paired quadratic elimination, and the exterior-square infinitesimal map with
its proved matrix/tangent identity. SU(5) supplies the bounded application.

### Physical Boundary And Stop Decision

The extra inputs are substantive: the background, nonzero real coupling and
background parameter, the definition of the mass operator as `g^2 ad_D^2`,
and the paired quadratic action with its chosen normalization. The pilot does
not derive these bosonic inputs from an SU(5) Higgs kinetic term or potential,
nor prove that a full Hermitian UV Lagrangian restricts to this action.
Positive M does not establish that external energies are small compared to M.

`orderedWilson` fixes the current order (q,u,q,e). The ordered tensor is
evaluated in q,q,u,e slots through the explicit matching identity. Its
alternation is checked, but a Grassmann reordering theorem for a full UV
action and agreement with a published Wilson-basis sign/factor are not proved.
Consequently the result is generation in the specified local algebraic model,
not an unconditional physical Wilson coefficient for every SU(5) model.
Other heavy fields, interference, derivative corrections and amplitudes are
not covered. No conclusion about proton instability or lifetime follows.

Stop here: the frozen algebraic endpoint is closed. Deriving the bosonic model
and full fermionic action from a UV Lagrangian would require a separately
approved scope. No additional library, custom axiom, `sorry`, dependency change
or heartbeat increase was used.

### Verification

- Focused builds of `GUT.SU5.Matching.TreeMatching` and the four relevant audit
  modules passed. The persistent audits check 7 generic elimination/mass,
  4 vector, 5 exterior-coordinate and 21 SU(5) declarations transitively;
  only `propext`, `Classical.choice`, `Quot.sound` are permitted.
- `lake build`: passed, 5779 jobs, including the previous current-block audit.
  Existing warnings were replayed; new/modified proof files have no warnings.
- `node tools/layout/check-layout.mjs`: passed, 728 modules.
- `node tools/docs/check-links.mjs` and `git diff --check`: checked before
  integration and repeated on the merged state.
- `python3 tools/qque/audit_one_generation.py`: 4 tests passed.
- `python3 tools/qque/audit_pairwise.py`: 3 tests passed.
- `python3 tools/qque/audit_contraction_uniqueness.py`: 3 tests passed.
  These exact finite regressions check the existing qque conventions; they
  are not independent verification of the newly chosen bosonic model.
- Integration target is master; Git ancestry records the topic and merge
  commits. Keep the topic branch; no remote push is authorized.
