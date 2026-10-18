# Exact SM Spectrum To Exterior Qque

- ID: exact-sm-spectrum-qque
- Status: completed
- Result type: proved spectrum-only alternating/exterior qque endpoint.
- Working branch: `proof/exact-sm-spectrum-qque`.
- Integration target: `master`, only after the endpoint and audit gates close.

## Frozen Endpoint

Retain finite-dimensional matter with strictly commuting ambient G and compact
H actions, torus unitarity, the original symmetric T x H invariant mass, two
actual conjugations and a compatible continuous SM-cover x H action on its
unchanged radical K. Replace user-supplied residual targets and both target
packages by a positive integer n and an SM-equivariant linear equivalence
from K (forgetting H) to exactly n copies of the five left-chiral SM species
plus any finite number of SM singlets.

Derive a qque-originating nonzero alternating coefficient on actual light
fields, reusing the existing exterior construction. H may act nontrivially
on multiplicities and singlets; its targets must be extracted, not supplied.
An SM-only equivalence does not assert that H acts trivially.

This is a more convenient, spectrally narrower sufficient condition, not a
weakening that contains all existing sources. No assumption of common residual
quotients, species-index equalities, weight-index equalities or nonzero operator
is allowed as a substitute for the promised derivation.

## Steps And Gates

1. Define the exact finite SM spectrum; prove species separation and the
   relevant actual Hom-space multiplicities and absence of opposite species.
2. Identify the monitored torus sectors with actual SM multiplicities and
   derive both target packages, including continuity and Q nonzero.
3. Apply the existing actual-field exterior endpoint; add positive and
   zero-generation boundary controls, strict audits and full build.

Stop if a new physical input is necessary. The virtual-index extension,
arbitrary vectorlike additions, realistic masses and nonzero amplitudes are
excluded. Do not claim completion or merge a partial milestone. Preserve the
E6 literature boundary and all dependency pins.

## Verification And Resume

Lean LSP MCP is not available in this session; use source inspection and
focused Lean builds. Record checked declarations and commands here as work
progresses. The prior [connection](../full-sm-light-bridge/README.md) supplies
the consumer, not a proof of this new spectrum-to-target bridge.

### Result

`ExactSMSpectrumQque.exists_actual_alternation` and `exists_actual_exterior`
now have no four-weight or species-index premise and no user-supplied residual
target. The exact SM-only spectrum derives all of them. See the concise
[statement, proof map and boundaries](results.md).

The endpoint is closed; the virtual-index extension remains a separate future
topic. The result is a convenient but spectrally narrower route B entry, not
a new model or an assertion about arbitrary extra light matter.

### Checked First Milestone (`checkpoint 01`)

- [FiniteSpectrum](../../../Math/RepresentationTheory/Multiplicity/FiniteSpectrum.lean)
  gives finite copies, Hom-space equivalences for products/copies and transport
  by a gauge-only equivalence. It does not supply a residual action.
- [ExactSMSpectrum](../../../Physics/StandardModel/Spectrum/ExactSMSpectrum.lean)
  defines exactly n complete left-chiral SM generations plus s singlets.
  Hypercharge separation and the existing Q/up/e irreducibility prove their
  actual Hom multiplicities are n and the three opposite multiplicities vanish.
- [ExactSMResidualSpectrum](../../../Physics/StandardModel/Spectrum/ExactSMResidualSpectrum.lean)
  extracts canonical targets as actual SM Hom spaces with the induced H action.
  Their Q/up/e dimensions, Q nonzero when n > 0, continuity and the three
  species-index equations are derived. The singlets' H action is unrestricted.
- [ExactSMSpectrumQque](../../../Physics/StandardModel/Operators/ExactSMSpectrumQque.lean)
  connects to actual alternating/exterior qque under the still-explicit
  `FourWeightLightQque.HasTarget` condition on these canonical targets.
  These `_of_four_weights` theorems remain as intermediate interfaces. Their
  new unsuffixed companions are the completed spectrum-only endpoints.

### Closed Weight Bridge

`ExactSMWeightMultiplicity` computes the actual torus character from the same
SM-only spectrum. It proves positive-weight dimensions n and opposite-weight
dimensions zero for every SM slot, including n = 0 and arbitrary s.

`ExactSMWeightEvaluation` constructs H-equivariant evaluation into the actual
light sectors. Concrete nonzero vectors in `MonitoredSMWeights`, irreducibility
and the dimension computation make these maps isomorphisms at 0, 3, 8, 14.
`ExactSMFourWeightTarget.has_target` derives the required equations for every
h in H. The comparison itself requires neither H compactness/continuity nor
conjugations; those retained inputs enter the final nonzero coefficient step.

### Verification

- Focused builds passed for `ExactSMFourWeightTarget` and dependencies;
  the full build checked the final adapter and persistent audits: 9 strict
  transitive axiom checks for finite spectra and 35 for the SM spectrum/adapter,
  standard three axioms only. Import-layer checks remain strict.
- Lean controls cover one generation, three generations plus seven singlets,
  absence of opposite species/weights for all n/s, zero-generation Q triviality,
  singlet separation and total dimension `15*n+s`. These are not ambient-GUT
  endpoint instances.
- `lake build` passed (5685 jobs). Existing unrelated warnings remain; the new
  sources have no warnings. No dependency pins or heartbeat limits changed.
- `python3 tools/qque/audit_one_generation.py`: four exact tests passed.
- `node tools/layout/check-layout.mjs`: 648 modules, passed.
- `node tools/docs/check-links.mjs`: 263 Markdown files, local links and
  33 fragments, zero errors. `git diff --check`: passed.
