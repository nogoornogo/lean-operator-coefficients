# Yukawa Families And Exact Light Spectra

- ID: yukawa-family-spectrum
- Status: completed
- Checkpoint detail: completed (integration recorded by Git after verification).
- Working branch: `proof/yukawa-family-spectrum`.
- Integration target: `master`.
- Result type: coupling classification and specified-family spectrum.

## Frozen Endpoint

Use the existing full-SU(6) `StandardSMUVYukawa` scalar/matter/coupling and
vacuum. Construct the family obtained by varying the Yukawa coefficient and
vacuum amplitude, with zero bare mass. Determine its entire radical as a
representation, including zero-parameter strata, not only an inclusion or
dimension bound. Preserve the existing nonminimal symmetric-scalar boundary.

Classify ALL scalar-linear symmetric invariant Yukawa couplings for specified
scalar and matter representations by an explicit bijection with intertwiners
from the scalar to the symmetric-form representation. For the existing SU(6)
scalar equivalence this gives an endomorphism parameterization. This is not
a numerical decomposition into irreducible Higgs multiplets or a claim that
the one-parameter coupling family exhausts all allowed couplings. Spectrum
claims cover the stated coupling/vacuum family, not every endomorphism.

Reuse the actual 27-dimensional UV source and its proved 15-dimensional light
representation. Derive mass evaluation before the radical conclusions. Supply
reusable scaling/spectrum lemmas in Physics. No potential minimization,
new model selection, UV-realizability assertion for arbitrary IR masses,
decay amplitudes, dependencies or axiom changes. Stop if new foundational
or physical assumptions are needed.

## Interfaces

- [Existing UV source](../../../GUT/SU6/SelectionRules/Models/StandardSMUVYukawa.lean)
- [Unitary scalar](../../../GUT/SU6/Yukawa/UnitarySymmetricScalar.lean)
- [Symmetric scalar representation](../../../Physics/FieldTheory/Yukawa/SymmetricScalarYukawa.lean)
- [Yukawa API](../../../Physics/FieldTheory/Yukawa/WeylYukawaMass.lean)
- [Actual light representation](../../../GUT/SU6/SelectionRules/Models/StandardSMUVMass.lean)

## Results

[YukawaClassification](../../../Physics/FieldTheory/Yukawa/YukawaClassification.lean)
constructs mutually inverse maps between all `EquivariantYukawa rhoS rhoV`
and `IntertwiningMap rhoS (SymmetricScalarYukawa.scalarRho rhoV)`. Symmetry
puts the image in the symmetric-form subrepresentation; full-group invariance
proves equivariance. Conversely every such intertwiner defines an allowed
coupling. The inverse laws prove exhaustiveness and uniqueness, not merely
existence of one tensor. No finite-dimensionality or semisimplicity is needed.
When the scalar is equivalent to that symmetric-form representation,
`endomorphismEquiv` gives an exact parameterization by its equivariant
endomorphisms. This does not compute a constituent decomposition, numerical
dimension or basis of the endomorphism space.

[GeneratedMassFamily](../../../GUT/SU6/Yukawa/GeneratedMassFamily.lean)
applies this parameterization to the existing unitary SU(6) scalar and actual
15 + 2 bar6 matter. Its selected family is Y_y = y Y_0, v_t = t v_0, with
zero bare mass; the declared SM x H group fixes every v_t. `mass_eq` first
derives B(y,t) = (y*t) B_0 from Yukawa evaluation.

- For y*t nonzero, `lightEquiv` identifies the ENTIRE radical equivariantly
  with the existing all-left-handed 15-dimensional SM representation.
- For y*t zero, `zeroLightEquiv` identifies it with the entire restricted
  27-dimensional UV matter representation.
- `radical_finrank` covers all complex y,t; `fifteen_iff` and
  `mass_nonzero_iff` give the exact condition y != 0 and t != 0.
- `light_preserved` keeps the old radical at every parameter, including the
  boundary where additional zero modes occur. `light_character` gives the
  full residual character in the nonzero stratum.
- `original_mass`, `coupling_off` and `vacuum_off` check the original point
  and the two distinct degenerations.

[ScaledMassSpectrum](../../../Physics/FieldTheory/Mass/ScaledMassSpectrum.lean)
supplies reusable representation-level radical equivalence and character
preservation. No diagonalization or numerical eigenvalues are used.

The fixed coupling/vacuum directions are those of the existing nonminimal
symmetric-scalar completion, whose vacuum encodes the chosen invariant mass.
This is not a newly derived minimal Higgs theory, a dynamically selected
vacuum, or a claim that all classified endomorphisms have this spectrum.
Other allowed couplings are parameterized by `allCouplings`; their spectra
require evaluating those maps at a vacuum. This pilot does not compute a
full rank stratification over that entire endomorphism space.

## Sources And Verification

No web search or external literature was used in this topic. Source provenance:
the linked `WeylYukawaMass` supplies the coupling/vacuum semantics;
`SymmetricScalarYukawa` supplies the symmetric-form action;
`StandardSMUVYukawa` and `UnitarySymmetricScalar` supply the full-SU(6) coupling
and specified vacuum; `StandardSMUVMass` supplies the original radical/SM
identification. New classification and scaling statements are proved directly
in Lean from those definitions. No literature statement is used as a premise.

Lean LSP unavailable; used source inspection and builds. Initial namespace,
extensionality and concrete-kernel elaboration errors were corrected by explicit
maps and generic lemmas. No new heartbeat setting, dependency or axiom change;
existing imported files retain their prior settings. No scripts were needed.
- Focused `lake build Physics.FieldTheory.Yukawa.Audit.AuditYukawaClassification
  GUT.SU6.Audit.AuditGeneratedMassFamily`: passed, 16 + 15 strict transitive
  axiom checks, allowing only propext, Classical.choice, Quot.sound.
- Full `lake build`: passed, 5844 jobs. No new source warnings; existing
  dependency warnings replayed.
- `node tools/layout/check-layout.mjs`: passed, 793 modules.
- `node tools/docs/check-links.mjs`: passed, 299 Markdown files, 1812 local
  links, 33 fragments. `git diff --check`: passed.
- No qque contraction/statistics or exchange definitions changed, so their
  separate exact regression scripts were not rerun. Source-controlled Lean
  controls verify the original mass point and both zero-parameter cases.
Commit and no-ff merge to master after verification; retain branch, no push.
