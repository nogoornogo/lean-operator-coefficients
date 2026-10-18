# QQue Spinor And Exterior Endpoint

- ID: qque-lorentz-exterior
- Status: completed
- Result type: proved under the existing compact-source and explicit SM-adapter inputs.
- Working branch: `proof/qque-lorentz-exterior`.
- Integration target: `master`.

## Frozen Endpoint

Under the unchanged compact-H source and explicit compatible SM decomposition
inputs, construct a nonzero invariant functional on the fourth exterior power
of the sum of actual Q, up-right and electron-right field spaces, including
left/right Weyl spinor factors. Invariance is under the SM covering group,
H and SL(2,C) acting on left spinors by g and right spinors by entrywise
conjugate g. This is a local algebraic fermionic coefficient, not a quantum
operator, Wilson coefficient, amplitude, vacuum theorem or lifetime bound.

No extra generation bound, nonzero coupling, split quotient or favorable
exchange-symmetry certificate may be assumed. Reuse the source-derived common
quotient and one Q identification twice. Do not prove a general Lorentz-cover
classification or change dependencies/E6 boundaries.

## Bounded Implementation

1. Explicit SL(2,C) spinor actions and epsilon intertwiners.
2. Reusable four-slot alternation on the sum of three field spaces and exterior
   descent, with the two identical-species slots treated correctly.
3. Symmetric residual coefficient, gauge/spinor combination and nonzero witness.
4. Transport to actual light fields, strict audits, regression tests, docs.

Stop if a new source assumption is required. Verified intermediate milestones
may be committed here; merge only after the endpoint and verification gates.

## References

- [Limited audit and remaining tasks](../qque-lorentz-statistics/results.md).
- [Existing SM adapter](../../proof/current/applications/Physics/EXPLICIT_SM_RESIDUAL_TENSOR.md).
- [Verification workflow](../../architecture/WORKFLOW.md).

## Verification

- `lake build`: passed, 5660 jobs. Existing style/deprecation warnings in
  unchanged sources remain; the new modules introduce no warnings.
- Focused endpoint and feasibility builds: passed. Strict transitive audits:
  exterior endpoint/controls 18 declarations, mathematical alternation/pairing
  13, external tensor transport 9, retained statistics probes 10. Only
  `propext`, `Classical.choice`, `Quot.sound` are permitted, with no exceptions.
- `python3 tools/qque/audit_one_generation.py`: all four tests passed,
  including exact all-component alternation/Grassmann correspondence.
- `node tools/layout/check-layout.mjs`: 623 modules; layer, cycle, import,
  aggregate and relocation checks passed.
- `node tools/docs/check-links.mjs` and `git diff --check`: passed.
- LSP MCP was unavailable. Focused builds and source inspection were used.
  Initial elaboration and instance-search failures were resolved by named
  coefficient interfaces and local caching of existing tensor group instances,
  not by adding theorem assumptions or increasing the trust boundary.

## Result And Stop Condition

All four planned steps are closed. See the
[statement and proof map](../../proof/current/applications/Physics/LORENTZ_EXTERIOR_QQUE.md).

`CompactLightExteriorQque.exists_ordered_nonzero_exterior` proves that the
ordered actual qque spinor-field coefficient has a nonzero alternating descent.
`exists_qque` gives the resulting nonzero SM-cover x H x SL(2,C) intertwiner
on the fourth exterior power of the direct sum of participating actual fields.
The witness has value 4 with the unnormalized symmetric residual coefficient;
the one-generation control and S3/A4 controls pass. The old unit-flavor
calculation's value 2 is retained and agrees after this explicit rescaling.

No new source assumption, minimum of two generations, interaction coefficient,
or arbitrary-radical full-SM lift was added. The existing SM decomposition is
still an explicit adapter input. Quantum dynamics, actual amplitudes, a general
Lorentz-cover classification, duql exterior coefficients and E6 topology remain
outside this endpoint. No further foundational project is opened.

Integration target remains `master`; Git ancestry records the completed merge.
