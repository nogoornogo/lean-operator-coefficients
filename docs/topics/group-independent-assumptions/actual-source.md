# Actual Source Checkpoint

- Status: construction verified; spectrum bridge now closed in the linked endpoint
- Working branch: `proof/group-independent-assumptions`
- Previous checkpoint: `checkpoint 01` (charge and supported-spectrum counterexample)
- Scope: finite SM representation and zero mass; [spectrum endpoint](spectrum-bridge.md)
  supplies the subsequent full comparison and actual-source counterexample

## Constructed Objects

[LeptonTrialitySource.lean](../../../Physics/StandardModel/Spectrum/LeptonTrialitySource.lean)
uses only Math/Physics and existing dependency packages. Names below are in
`GUT.LeptonTrialitySource`, retaining the repository's namespace convention.

The SM gauge group is the existing covering product `SU(3) x SU(2) x Circle`,
with integral hypercharges `6Y`. No UV unification action or SU(5) orbit
compatibility is supplied. A global SM quotient identification is not asserted
by this checkpoint.

- `generation`: `quark`, `upRight.dual`, `downRight.dual`, `lepton`,
  `electronRight.dual`, charged respectively by `(0, 0, 0, label, -label)`.
- `matter`: three copies of that direct product, with an explicit finite basis.
- `generation_coefficients`, `matter_coefficients`: continuous matrix
  coefficients, derived from the actual gauge matrices, tensor product,
  contragredients, circle phases and finite residual characters.
- `unitaryModel`, `modelEquiv`: an equivalent continuous unitary realization
  using the existing finite-basis compact-group unitarization theorem.
- `model_jointlyContinuous`, `model_unitary`, `model_finrank`: the action is
  jointly continuous, preserves its inner product, and has complex dimension 45.
- `gauge_residual_commute`: the SM and residual actions commute on this model.
- `mass`, `radicalEquiv`, `radical_finrank`: invariant zero symmetric mass whose
  radical is equivariantly the original 45-dimensional matter representation.

## Derived Character And Actual Vectors

`generationTrace (g,h)` is the sum of the five actual species trace characters,
with inverse gauge elements for the contragredient fields and residual phases
`character h` and its inverse on the two lepton blocks.

`radical_character_formula` proves that the actual radical trace is three times
this explicit expression. `radical_dual_character_formula` proves the matching
antisymmetrized trace formula. These are full-group trace identities, not supplied
light-target assumptions.

`generation_residual_basis` and `matter_residual_basis` compute the finite-group
action on the explicit matter basis. `exists_charged_zeroMode` transports that
basis through `radicalEquiv` and gives a nonzero radical vector of the assigned
residual character for every basis index. This checks actual vectors but does
not yet assert their joint SM torus weights.

## Subsequent Endpoint

The [spectrum checkpoint](spectrum-bridge.md) completes the physical-torus trace
comparison, identifies the full actual radical spectrum by faithful evaluation,
and transfers the supported prohibition. Joint SM-weight/residual eigenvectors
and a closed actual-source witness are now proved there. The declarations in
this construction file retain their original narrower statements.

No quantum anomaly theorem, realistic nonzero mass spectrum, proton lifetime,
or nonzero decay amplitude is claimed. The zero mass is intentional and was
admitted by the frozen scope; the 45-dimensional radical is nonempty.

## Construction Checkpoint Verification

Focused build and strict transitive audit passed:

```sh
lake build Physics.StandardModel.Spectrum.Audit.AuditLeptonTrialitySource
```

[AuditLeptonTrialitySource.lean](../../../Physics/StandardModel/Spectrum/Audit/AuditLeptonTrialitySource.lean)
checks 19 declarations, allowing only `propext`, `Classical.choice`, `Quot.sound`.
It also checks the actual inner product identity, mass invariance, dimension,
joint continuity and nonzero radical vectors at their consumer types.

Also passed:

```sh
lake build
node tools/layout/check-layout.mjs
node tools/docs/check-links.mjs
git diff --check
```

Full build: 5550 jobs. Layout: 534 modules with no upward imports or missing
aggregate entries. Links: 221 Markdown files, 1160 local links, no errors.
The new source/audit files have no warnings; unchanged modules retain their
previous warnings. No dependency pins, existing theorems, or axiom allowlists
were changed. No temporary Lean source is needed to reproduce this checkpoint.
