# Georgi-Glashow Matter To Actual Exterior Qque

- ID: georgi-glashow-exterior
- Status: completed
- Checkpoint detail: completed. Started/completed: stage 01.
- Working branch: `proof/georgi-glashow-exterior`.
- Integration target: `master`.

## Frozen Scope

Use the retained actual SU(5) matter `n(10 + bar5)`, with `n > 0`,
and a continuous compact ordinary internal group acting through its unitary
centralizer. The zero symmetric mass retains this pre-electroweak chiral
matter. This is a fermion-sector benchmark, not a modified particle spectrum
or a construction of a complete interacting Georgi-Glashow model.

Derive the compatible SM-cover action, exact SM spectrum, and positive
constituent condition rather than accepting these as new model certificates.
Connect them to a nonzero qque alternating/exterior coefficient on actual
participating fields. Vacuum selection, Yukawa couplings, anomaly consistency,
Wilson coefficients and decay rates are explicitly excluded.

## Deliverables And Stop Gate

1. Construct the arbitrary-group joint action and actual SM branching adapter.
2. Derive positive constituent support from the retained spectrum and conjugations.
3. Apply the actual-field exterior endpoint and audit its transitive axioms.
4. Focused/full builds, layout/link checks and relevant computational controls.

No new foundations or dependency changes are authorized. Stop if the existing
branching and compact representation APIs cannot supply a required interface;
do not replace a missing interface with an assumption and claim completion.

## Result

Proved. The actual retained matter now derives the compatible continuous
SM action and exact spectrum. The normalized species presentation has a
shared positive constituent and therefore satisfies the pairwise condition.
The automatic-species endpoint gives actual nonzero qque alternation and
exterior descent. No target, normalized presentation, species matching,
positive support, splitting or field decomposition is an additional input.

- [Source](../../../GUT/SU5/SelectionRules/GeorgiGlashowSource.lean):
  existing SU(5) Hilbert matter, general centralizer action, zero radical,
  and branching by composition of existing representation equivalences.
- [Application and controls](../../../GUT/SU5/SelectionRules/GeorgiGlashowQque.lean):
  shared/pairwise positivity and actual exterior endpoint; PUnit controls for
  one and three generations, with actual species multiplicities `(n,n,n)`.
- [Reusable extraction](../../../Physics/StandardModel/Spectrum/ExactSMAutomaticPositive.lean):
  exact SM spectrum and two conjugations imply positive automatic support.
- [Precise scope](../../proof/current/applications/GUT/GEORGI_GLASHOW_QQUE.md).

All bounded deliverables are closed. The result remains a zero-mass
fermion-sector benchmark, not a Yukawa/vacuum construction, executable irrep
classifier or decay-rate prediction. Existing proof and dependency pins are
unchanged. Integration follows the recorded target; Git ancestry records the
topic and no-ff merge commits.

## References

- [Retained SU(5) selection rule](../../proof/current/applications/GUT/SU5_SELECTION_RULE.md)
- [Exact-spectrum endpoint](../exact-sm-spectrum-qque/results.md)
- [Automatic presentations](../normalized-virtual-presentation/README.md)
- [Alonso et al., section III.B](https://arxiv.org/abs/1405.0486)

## Verification

Verified at stage 01:

- `lake build GUT.SU5.Audit.AuditGeorgiGlashowQque Physics.StandardModel.Spectrum.Audit.AuditExactSMAutomaticPositive`:
  passed, 4061 jobs. Fifteen model declarations and two extraction declarations
  passed transitive axiom checks; only `propext`, `Classical.choice`, `Quot.sound`
  are permitted. The physics import-origin audit passed.
- `lake build`: passed, 5720 jobs. Existing dependency warnings remain; no new
  source warnings, sorry, custom axioms or enlarged heartbeat limits.
- `python3 tools/qque/audit_one_generation.py`: four exact tests passed.
- `python3 tools/qque/audit_pairwise.py`: three exact tests passed.
  These computational controls supplement, not replace, the Lean proofs.
- `node tools/layout/check-layout.mjs`: 675 modules, passed.
- `node tools/docs/check-links.mjs`: 274 Markdown files, 1556 local links,
  33 fragments, zero errors.
- `git diff --check`: passed. No unrelated changes or pin changes.

Lean LSP MCP was unavailable. Source inspection and focused Lean builds were
used instead. Initial direct expansion of the concrete branching equivalences
hit elaboration/kernel limits; composing existing representation equivalences
closed the same statement under the unchanged verification limits.
