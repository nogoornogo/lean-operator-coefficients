# Mediator To Full Light-Species Certificate

- ID: mediator-full-light-certificate
- Status: completed
- Checkpoint detail: completed (integration recorded by Git).
- Working branch: `refactor/mediator-full-light-certificate`.
- Integration target: `master`.
- Result type: reusable proof interface and checked SU(5) application.

## Frozen Endpoint

Extract the already checked SU(5) generated-exchange/completeness connection
into Physics, independent of GUT. Inputs are a supplied finite-dimensional
SM x H light representation, mediator mass and currents on its canonical
full Q/up/e species, proved joint invariance and a nonzero alternating slot
evaluation. Supply a restriction-based constructor so models reuse their
derived current restrictions and concrete probe calculation.

Derive the generated sector's nonzero value and, under SM semisimplicity,
the residual Hom, its nonzero value and exact reconstruction of the SAME
generated sector. Refactor the SU(5) nonzero proofs to consume this API.
Do not assume nonzero generated sector or nonzero residual Hom as input.

The certificate does not discover light fields, derive current restrictions,
prove invariance for arbitrary models, or turn radical protection into
operator generation. No UV, amplitude, pin or axiom changes. Stop if the
abstraction changes the existing SU(5) coefficient or requires new hypotheses.

## Interfaces

- [Evaluation](../../../Physics/StandardModel/Operators/MediatorQqueEvaluation.lean)
- [Completeness](../../../Physics/StandardModel/Operators/FullLightSpeciesQque.lean)
- [SU(5) connection](../../../GUT/SU5/Matching/LightSpeciesCompleteness.lean)
- [Light coherence record](../light-matching-coherence/joint-species.md)

## Results

[MediatorFullLightCertificate](../../../Physics/StandardModel/Operators/MediatorFullLightCertificate.lean)
contains no GUT import. A certificate stores proved joint invariance, explicit
field/spinor evaluation points and the nonzero antisymmetrized exchange
evaluation. The underlying mediator mass and currents are parameters on the
canonical full species of tau; a nonzero exterior sector is not an input.

`ofRestriction` builds this evidence from maps into the canonical species,
a reference coefficient, a proved restriction formula and a calculated probe.
The maps need not be assumed injective or individually equivariant: the
restriction/probe proves what is needed for nonzero descent, while the full
current's invariance is a separate obligation. This does not certify a model's
physical field interpretation merely from arbitrary linear maps.

`Certificate.generated_nonzero` derives nonzero exterior descent. Under the
existing finite-dimensional/SM-semisimple completeness hypotheses,
`residualHom_nonzero` and `reconstruct` give the nonzero residual map and
recover exactly the generated exchange. Existence wrappers are included.
The basic probe-to-nonzero step itself requires no finite-dimensionality.

The SU(5) application now builds this certificate from its unchanged actual
radical currents, derived SM x H invariance, generation restriction formula
and original probe calculation. Both nonzero proofs consume the generic API.
`certificate_generated` and `certificate_residualHom` prove by reflexivity
that the old coefficient and residual map are unchanged. The old reconstruct
statement remains valid even for zero generations, when no nonzero certificate
is supplied. One/three-generation controls remain checked.

This is a reusable interface for an existing conclusion, not a new physical
generation theorem. It is separate from invariant mass protection: that
classification supplies radical preservation, not the current/probe obligations.
No automatic application to Spin(10), E6, arbitrary SUN light spectra, UV
Yukawa families or physical decay amplitudes is claimed.

## Verification

- Focused certificate and SU(5) audit builds passed, 6 + 42 strict transitive
  checks allowing only propext, Classical.choice, Quot.sound. Final full build
  rechecked both after removing unused finite-dimensional hypotheses.
- Full `lake build`: passed, 5839 jobs. No new source warnings; existing
  dependency warnings replayed.
- Exact regressions: `audit_one_generation.py` (4), `audit_pairwise.py` (3),
  `audit_contraction_uniqueness.py` (3), all under tools/qque: passed.
- Layout: passed, 788 modules. Links: passed, 298 Markdown files, 1800 local
  links, 33 fragments. `git diff --check`: passed.
- Initial elaboration of a nested existential probe timed out; explicit
  evaluation-point fields removed that elaboration cost. No heartbeat or
  dependency change. The existing concrete SU(5) suggestion-index exclusion
  remains unchanged; no new search-index exclusion was added.
- Lean LSP unavailable; used source reads and builds.
- Commit and no-ff merge to master, retain branch, no push; recheck merged state.
