# Delta-B = 2 Grading And Six-Quark Feasibility

- ID: `delta-b-two`
- Status: completed
- Result type: proved existence pilot and positive bounded feasibility decision
- Working branch: `proof/delta-b-two`
- Integration target: `master`
- Integration policy: merging into `master` requires explicit user direction

## Endpoint And Scope

Establish a bounded algebraic pilot for one-generation, derivative-free
`Delta B = 2` six-quark operators. The approved work has three stages:

1. Define baryon-number grading and residual ordinary-Abelian character tests,
   and apply them to the physical right-handed `uudd dd` monomial.
2. For one all-right-handed species/chirality sector, construct an explicit
   Standard-Model-cover and Lorentz invariant color/spinor contraction and
   prove that its six-field alternating/exterior descent is nonzero.
3. Compare the construction with a published `n`-`nbar` operator basis and
   decide whether contraction relations, an inverse map and a qque-style
   coefficient-completeness theorem are feasible with the pinned foundations.

The stage-2 target is the species degree `(2 upRight, 4 downRight)` in physical
right-handed conventions, with total `6Y = 0`, `3B = 6`, lepton number zero and
canonical dimension nine. The first construction may use a convenient
epsilon-product representative in the span of the conventional all-right-handed
`uudddd` contractions; identifying an exact literature normalization is a
stage-3 obligation, not an assumption in the existence proof.

RGE evolution, perturbative or nonperturbative QCD, hadronic/neutron matrix
elements, lattice computation, oscillation times, rates, phenomenological
bounds, UV matching and numerical simulation are out of scope. The theorem is
about an allowed nonzero local coefficient, not a generated interaction or an
observable transition.

## Deliverables And Acceptance

- A registered `Physics` module for six-slot quantum numbers, baryon grading,
  residual character neutrality/prohibition and the concrete `uudddd` control.
- A six-slot alternating/exterior construction with explicit two-color-epsilon
  and three-Weyl-epsilon contraction, plus a one-generation nonzero witness.
- Persistent strict transitive axiom audits and exact lightweight regression
  checks where useful; no external numerical packages or floating point.
- A short feasibility result matching the proved contraction to the literature
  conventions and stating a yes/no bounded route to coefficient completeness.
- Focused builds, layout/link checks, strict audits and a full `lake build`.

Stop after stage 3 with a proved result or a scoped feasibility decision. Stage
4, a complete basis theorem for finitely many specified sectors, requires new
user approval even if feasibility is positive. It must not start by renaming a
new foundational project or importing QCD calculations.

## Work And Open Obligations

- Completed the grading and residual-character pilot.
- Completed the explicit all-right-handed exterior coefficient and nonzero
  witness.
- Completed the literature correspondence and bounded completeness feasibility
  decision; see [the result](feasibility.md).
- The separately approved [completeness child](../delta-b-two-completeness/README.md)
  now proves the intrinsic all-right degree `(2,4)` sector is two-dimensional,
  with two evaluation probes and their explicit inverse. It integrates back
  into this parent; integration into `master` still requires explicit direction.

## Result And Verification

The `uudddd` control is a dimension-nine, gauge-neutral, all-right-handed
six-quark monomial with `3B = 6`. Its residual charge is
`-(2 up + 4 down)`, giving an exact ordinary-Abelian prohibition criterion.

The existence pilot constructs the literature `O^3_RRR`-pattern `AAS` color
tensor and three right-Weyl epsilon contractions. The ordered tensor is
Standard-Model-cover and Lorentz invariant. Its sixth-exterior-power descent
has an explicit one-generation evaluation equal to `24`, hence is nonzero.

The feasibility gate is positive only for a separately approved,
one-generation, derivative-free all-right sector. A completeness theorem would
need both the proved `AAS/O^3` direction and an independent `SSS` direction,
plus finite classification and Fierz lemmas. That stage was not part of the
original feasibility milestone; the subsequently approved child now supplies
the intrinsic two-coordinate equivalence. Its verification is recorded separately.

Focused verification passed:

- `lake build Physics.StandardModel.Operators.DeltaBTwoLocalOperator Physics.StandardModel.Operators.Audit.AuditDeltaBTwoLocalOperator`
- `lake build Math.RepresentationTheory.Audit.AuditSixSlotAlternation Physics.StandardModel.Operators.Audit.AuditDeltaBTwoSixQuark`
- strict audits: 6 six-slot declarations and 7 six-quark declarations passed;
  the earlier grading audit covers 7 declarations.
- `node tools/layout/check-layout.mjs` passed with 881 registered modules at
  the existence milestone.

Final endpoint verification passed:

- `lake build` completed successfully with 5934 jobs; pre-existing repository
  lint/deprecation warnings remain, with no new failure.
- `node tools/layout/check-layout.mjs` passed with 881 modules.
- `node tools/docs/check-links.mjs` passed with 331 Markdown files, 2022 local
  inline links and 33 heading fragments.
- `git diff --check` passed.

The user authorized integration into `master` after completion of the
two-coordinate child; merge `checkpoint 01` records that integration. The
existence/feasibility checks above remain historical;
the completed classification's checks are in the
[child record](../delta-b-two-completeness/README.md). Topic branches are retained,
and Git ancestry records integration.

The integration-status correction is documentation-only: link and diff checks
are rerun, with no Lean rebuild for that edit. The merged state is checked
separately below.

### Master integration verification

- `lake build` passes on the merged state (5950 jobs).
- Focused strict audits for `AuditSixQuarkTwoCoordinates`,
  `AuditSixQuarkInvariant`, `AuditSixColorInvariant`, and
  `AuditSixSlotRestrictionLift` pass, including the final 23-check audit.
- `python3 tools/delta-b-two/species-quotient.py` reproduces the exact
  rank-23 system and its two kernel vectors without external dependencies.
- Layout checks pass for 897 modules; documentation checks pass for 337 files
  and 2043 local links. `git diff --check` passes.
- This verification-record edit is documentation-only; link and diff checks
  are rerun, without another Lean build. No remote push is performed.

## References

- [Standard local operator conventions](../../../Physics/StandardModel/Operators/StandardModelLocalOperator.lean)
- [Existing four-slot alternation](../../../Math/RepresentationTheory/FourSlotAlternation.lean)
- [Qque completeness boundary](../qque-coefficient-completeness/README.md)
- [Basis correspondence and feasibility decision](feasibility.md)
- Rinaldi et al., [six-quark and chiral bases](https://arxiv.org/html/1901.07519#S2.SS1)
- Buchoff and Wagman, [operator renormalization and basis conventions](https://arxiv.org/abs/1506.00647)
