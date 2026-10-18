# SU(5) Current Blocks Pilot

- ID: su5-current-blocks
- Status: completed
- Result type: proved current-block pilot; positive feasibility result.
- Working branch: `proof/su5-current-blocks`.
- Integration target: `master`.

## Frozen Endpoint

Use SU(5) as a test of a reusable connection from an actual representation
to nonzero infinitesimal species blocks. For the existing ten (the actual
second exterior power), construct one compact off-diagonal direction and
prove that its actual exponential curve has nonzero electron-left to quark
and quark to up-left matrix coefficients at first order. Identify the input
and output species through the existing SM branching, not a new weight list.
Neither nonzero block is an input.

The mathematical input is the retained standard SU(5) representation and
embedding. A gauge interaction, nonzero gauge coupling, heavy vector mass,
vacuum and matching prescription are not reconstructed. This endpoint does
not claim a generated Wilson coefficient, an amplitude or a decay rate.

## Routes And Stop Condition

1. Differentiate the two-by-two minors of the actual exterior group action
   along the compact matrix exponential. Extract a generic minor derivative
   helper if it removes the common analytic calculation.
2. If needed, use polarization of the exterior functor to identify the same
   infinitesimal blocks, retaining a proved link to the group curve.

Stop with a scoped feasibility result if either route needs new foundational
machinery beyond these interfaces. Do not substitute arbitrary intertwiners
for the actual action, add nonzero-block assumptions, or change dependencies.
Review what the test establishes for reuse before proposing a broader project.

## Acceptance

Actual species identification, two nonzero first derivatives for the same
compact direction, persistent strict transitive axiom audits, focused and
full builds, layout/link/diff checks. Lean LSP is unavailable; use source
inspection and Lean builds. Existing qque contractions are unchanged.

## References

- [Existing fermion benchmark](../georgi-glashow-exterior/README.md)
- [Actual ten](../../../GUT/SU5/Representations/Matter.lean)
- [SM branching](../../../GUT/SU5/Branching/ExteriorSquare.lean)
- [Existing exponential calculation](../../../GUT/E6/Minuscule/SU5Exponential.lean)

## Result And Verification

The frozen endpoint is proved. No new nonzero-current or splitting premise
is supplied. In zero-based indices the compact direction is
`X = E(0,3) - E(3,0)`. The actual SU(5) curve is `exp(t X)`, acting through
the existing `Matter.ten`, not through a newly postulated matter action.

[CurrentBlocks](../../../GUT/SU5/Representations/CurrentBlocks.lean) proves:

- `electron_species`, `quarkOut_species`, `quarkIn_species`, `up_species`
  identify the four exterior-basis vectors through the existing SM branching.
- `quarkCoordinate_eq` and `upCoordinate_eq` identify the output probes on
  every vector with coordinates of the quark and up-left species projections.
- `species_derivatives` gives electron-left to quark derivative 1 and quark
  to up-left derivative -1 along the SAME actual compact group curve.
- `both_blocks_nonzero` concludes both first derivatives are nonzero.
- `cross_block_formula` gives the two entries for ANY fundamental matrix X:
  `X 0 3` and `-X 0 3`. The sign follows from the ordered exterior basis.
- `selected_tangents_zero_of_entry_zero` and `coefficients_at_zero` are negative controls:
  a vanishing cross entry kills these probes; at the identity the original
  inter-species coefficients vanish despite their nonzero first derivatives.

### Reusable Content And Boundary

[ExteriorSquareCoordinates](../../../Math/RepresentationTheory/ExteriorSquareCoordinates.lean)
works for every n, on the actual exterior square of `Fin n -> C`.
It constructs a basis, proves the two-by-two minor formula, and differentiates
every coefficient along any entrywise differentiable matrix curve through
the identity. It has no SU(5), SM, Physics or GUT imports. Its coordinate
construction follows the earlier E6/SU(5) exterior-coordinate calculation,
now parameterized by n; the earlier module is left unchanged.

This test establishes that actual action-to-species-current nonvanishing can
be derived with the pinned libraries, without adding two independent nonzero
couplings. It uses the concrete representation also used by the no-go source;
it is not a consequence of the selection-rule conclusion alone. The pilot
uses one ten, without a generation or general residual-action adapter.

A full derivative as a bundled Lie representation, transport to arbitrary
light subspaces in other GUTs, a gauge interaction and its normalization,
heavy masses and matching remain separate interfaces. In particular the
result does not yet construct a mediator exchange, a residual-invariant
four-fermion contraction, a nonzero Wilson coefficient or an amplitude.
No heavy mass follows from these nonzero current blocks. A future extension
would have to derive the matching contraction, not name its output in advance.
These are boundaries of the positive pilot, not remaining obligations for it.

### Checks

- `lake build Math.RepresentationTheory.ExteriorSquareCoordinates GUT.SU5.Representations.CurrentBlocks`:
  passed, including all species identifications and derivative statements.
- `lake build Math.RepresentationTheory.Audit.AuditExteriorSquareCoordinates GUT.SU5.Audit.AuditCurrentBlocks`:
  passed; 3 generic and 16 model strict transitive axiom checks. Only
  `propext`, `Classical.choice`, `Quot.sound` are allowed.
- `lake build`: passed, 5770 jobs. Existing warnings were replayed;
  no warnings in the four new Lean modules. No sorry, custom axiom, new
  dependency, changed pin or increased heartbeat setting.
- `node tools/layout/check-layout.mjs`: passed, 719 modules.
- `node tools/docs/check-links.mjs`: passed, 285 Markdown files and 1646
  local inline links; `git diff --check`: passed.
- Existing qque computational tests were not rerun: no qque contraction,
  alternation, normalization or prior definition was modified. The new
  controls are kernel-checked Lean theorems, not numerical samples.

Integration is tracked by Git ancestry into `master`; retain the topic branch.
