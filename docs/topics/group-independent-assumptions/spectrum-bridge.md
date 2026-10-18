# Actual Spectrum And Endpoint

- Status: Lean-checked; final verification recorded in the topic overview
- Preceding construction: [actual source](actual-source.md)
- Declaration namespace: `GUT.LeptonTrialitySpectrum`

## Result

[LeptonTrialitySpectrum.lean](../../../Physics/StandardModel/Spectrum/LeptonTrialitySpectrum.lean)
closes the actual-source bridge. This is a counterexample to removing the UV
unification/orbit conditions from the frozen finite mass interface, not to any
existing SU(5), SU(6), SU(N), Spin or E6-candidate theorem.

The model uses the SM covering gauge product `SU(3) x SU(2) x Circle`, three
ordinary SM generations (45 complex dimensions), and the finite residual group
`Multiplicative (ZMod 3)`. Its all-left-handed residual charges are
`(Q, u^c, d^c, L, e^c) = (0, 0, 0, label, -label)`.
The jointly continuous unitary action and its commuting gauge/residual factors
are constructed, not assumed. The invariant symmetric mass is zero, so the
whole matter space is the radical. Zero mass was explicitly allowed in the
frozen endpoint; empty matter or empty support was not.

`actual_source_counterexample` bundles this actual action with an invariant
mass and a spectrum satisfying all of:

- Radical dimension 45.
- The full joint torus/residual eigenspace spectrum is exactly the lift of the
  stated charge-resolved spectrum, with no omitted characters.
- Its dual chiral difference is exactly the target of three positive generations.
- The SM charge assignment is supported.
- `ForbidsEverySupportedPhysicalDeltaBOneOperator` holds.

The last predicate means the existing four-fermion, two-left/two-right,
dimension-six signature class. It does not quantify over every conceivable
baryon-violating operator. No anomaly cancellation, quantum completion,
realistic mass hierarchy, amplitude or lifetime is asserted. The SM global
quotient is not separately identified here.

## Proof Chain

1. `trace_target` computes the actual generation trace on the physical SM torus
   and proves equality with the fifteen-weight, three-generation target.
2. `radical_trace` transports the equality through the actual unitary model
   and its zero-mass radical.
3. `full_spectrum_eq` uses faithful evaluation of finite Abelian characters.
   This is stronger than matching dimensions or matching only dual indices.
4. `actualSpectrum` is defined from the actual radical eigenspace multiplicities
   by `Finsupp.comapDomain`, not by setting it equal to the desired target.
   `actualSpectrum_eq` proves that equality.
5. `actual_chiral_index` and `radical_dual_trace` give the coefficient and trace
   versions of the required light dual index.
6. `actual_forbids_all_supported` transfers the earlier exhaustive signature
   result to the actual spectrum. `exists_joint_zeroMode` supplies a nonzero
   radical vector for each of the fifteen joint SM-weight/residual characters.
7. `actual_not_weylInvariant` verifies that the removed UV orbit condition is
   genuinely absent, explaining compatibility with the retained no-go theorems.

## Shared Coordinates, Not A Hidden UV Hypothesis

Existing determinant-one torus coordinates, faithful character evaluation,
physical covering-torus coordinates and SM trace calculations were extracted
from four SU(5) files into Math/Physics. The old import paths and declaration
names remain compatible. Transferred declaration/proof bodies were mechanically
compared with the preceding commit and are unchanged.

The new `PhysicalTorus.gaugeHom` gives the actual SM diagonal action. The
surjectivity of the physical coordinate map makes the character-key map
injective. Using determinant-one coordinates is just a faithful encoding;
no extension of this matter representation to SU(5), and no Weyl invariance
of its charge-resolved spectrum, is postulated.

## Persistent Audit

[AuditLeptonTrialitySpectrum.lean](../../../Physics/StandardModel/Spectrum/Audit/AuditLeptonTrialitySpectrum.lean)
checks 19 declarations transitively, allowing only `propext`, `Classical.choice`
and `Quot.sound`. It also rejects imports of all `GUT` application modules and
checks actual nonzero radical vectors and mass invariance at consumer types.
Compatibility declaration namespaces beginning with `GUT` are not module imports.

```sh
lake build Physics.StandardModel.Spectrum.Audit.AuditLeptonTrialitySpectrum
lake build
node tools/layout/check-layout.mjs
node tools/docs/check-links.mjs
git diff --check
```

No new dependency, pin change, custom axiom, placeholder, or weakened audit
allowlist is used. New source modules are registered in `Math.lean` / `Physics.lean`.

## Decision

The group-free no-go is false under the frozen retained assumptions. The next
topic is the [structural conjugation criterion](../structural-conjugation/README.md):
identify sufficient common structural inputs, rather than silently adding
charge equalities to the group-free claim. That separate topic is not activated
by completion of this counterexample.
