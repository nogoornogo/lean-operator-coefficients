# Charge Counterexample Checkpoint

- Status: completed
- Scope: milestone 1 only; not the full finite-dimensional mass-source countermodel

## Statement

Lepton triality gives left-handed SM species charges `(0, 0, 0, 1, -1)` modulo
three. The physical right-handed charged lepton has charge `+1`. Both existing
proton-operator charge functionals equal `1`, not zero. Three copies of each
species give positive equal totals without forcing equal charge profiles.

The character witness uses mathlib's injective map from `ZMod 3` to `Circle`.
Supported charges equal the chosen assignment, so the existing signature
classification gives universal prohibition within the declared predicate.
`assignment_supported` separately exhibits nonempty support.

## Deliverables

- [LeptonTriality.lean](../../../Physics/StandardModel/Operators/LeptonTriality.lean):
  charge, character, profile and actual canonical gauge-tensor checks.
- [AuditLeptonTriality.lean](../../../Physics/StandardModel/Operators/Audit/AuditLeptonTriality.lean):
  finite group order and strict transitive axiom checks
  allowing only `propext`, `Classical.choice`, `Quot.sound`.

## Proved Endpoints

All declarations below are in `GUT.LeptonTriality`.

- `cyclic_charge_counterexample`: both operator charges are nonzero in `ZMod 3`.
- `character_injective`, `label_ne_zero`, `label_three_nsmul`: a faithful residual
  character of a group of order three, not an integer label without realization.
- `family`: positive common total of three for every species.
- `supported_iff`: the only supported charge assignment is the specified one.
- `supported_spectrum_counterexample`: correct uncharged target, nonempty support,
  universal prohibition, and failure of full rank-five Weyl invariance.
- `not_universal_family_obstruction`: positive common totals alone do not imply
  the no-go, expressed as an explicit negation of that universal claim.
- `canonical_tensors_not_invariant`: both canonical SM tensors are nonzero and
  fail residual invariance. This does not identify them with mass-radical tensors.

## Verification

Passed:

```sh
lake build Physics.StandardModel.Operators.Audit.AuditLeptonTriality
lake build
node tools/layout/check-layout.mjs
node tools/docs/check-links.mjs
git diff --check
```

The focused build passed 12 strict transitive axiom checks. Full build: 5547 jobs;
the build replayed 317 warnings in unchanged modules, with none in the new files.
Layout: 532 modules. Links: no errors. Lean LSP MCP was unavailable in the active
tool set, so validation used direct Lake/Lean builds. Dependency pins unchanged.

No mass-radical or quantum anomaly conclusion follows from this checkpoint
alone. Next: realize the spectrum as the oriented SM target whose difference
with its dual is the light dual index of an actual SM representation with
invariant mass. Neither E6 topology nor anomaly classification is needed for
this finite-dimensional endpoint.
