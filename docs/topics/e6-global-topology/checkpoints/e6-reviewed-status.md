# E6 Proof Status

Historical review snapshot, not a current work queue. Preserved from the retired
status directory; the [literature-boundary dossier](../../../proof/current/inputs/GUT/E6_LITERATURE_BOUNDARY.md)
owns the theorem's current inputs and interpretation.

Updated: stage 01

## Current Result

The candidate-group physical theorem remains kernel checked. Candidate simple
connectedness is now **kernel checked conditionally on an explicit literature
input**, not proved unconditionally. No new physical hypothesis is introduced.

See [E6 Literature Boundary](../../../proof/current/inputs/GUT/E6_LITERATURE_BOUNDARY.md) for the exact
external theorem, candidate inputs, mathematical named-E6 interpretation and
the distinction from a fully formalized global identification.

## Verification Layers

| Layer | Status |
| --- | --- |
| Concrete compact connected Lie group, tangent E6 real form, SU(5) inclusion | Kernel checked, preserved |
| Positive dual target and supported selection-rule result on the candidate | Kernel checked, unchanged |
| Closed maximal six-circle torus and all torus-loop contractions in G | Kernel checked, preserved |
| Maximal-torus inclusion induces a surjection on fundamental groups | External mathematical input: Raghunathan Proposition 38; not proved in Lean |
| That input implies `SimplyConnectedSpace compactIdentityComponent` | Kernel checked, explicit argument retained |
| Interpretation as conventional compact simply connected E6 | Literature-assisted mathematics, using Lie correspondence/compact real-form classification |
| Lean equivalence to a separately named global E6 carrier | Not constructed; outside the agreed boundary |

## Local-Prover Review

Delegation stopped by the user. Submission snapshot: `checkpoint 01`.

| Former item | Accepted result, not an inflated completion claim |
| --- | --- |
| L1 | Candidate and torus coset space path connectedness |
| L2 | Smooth torus inclusion; not quotient charts or bundle lifting |
| L3 | All-72-root torus regular condition, openness and explicit regular point; no global centralizer comparison |
| L4 | Closed torus singular locus and simple-root-kernel inclusion; no group codimension-three theorem |
| L5-L8 | Unproved/invalid drafts archived; not used as assumptions |
| Generic helpers | Valid centralizer sequential limit lemma, definition projections and covering/proper-map wrappers retained |

The rejected fixed-T regular locus, whole-torus regularity, nearby-centralizer
containment, and torus simple-connectedness claims are NOT accepted literature
facts. The original source and status report are retained in the
[review archive](../drafts/README.md).

## Verification

- Focused audit: `lake build Math.LieGroups.E6.Audit.AuditLiteratureTopology`, 3984 jobs.
- Full build: `lake build`, 5517 jobs, including the new audit via `GUT.lean`.
- New audit: 14 declarations; only `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry` or custom axiom in the replacement; literature input is a parameter.
- Pins unchanged. Retained older modules still emit existing linter warnings.

The successful audit proves the conditional implications, not the external
premise. Future work is in [Topic records](../../README.md), not an automatic restart of L5-L7.
