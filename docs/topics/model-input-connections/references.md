# Reusable Sources And Literature Roles

The listed assets are reused by the implemented shared constructors and named
consumers. [Source comparison](literature-validation.md) records the reopened
primary-source locations and their precise scope. No external theorem premise
or paper-wide validation is added.

## Mathematical And Physical Assets

| Source | Reuse and obligation |
| --- | --- |
| [BoundaryProjectors](../../../Math/LinearAlgebra/Boundary/Projectors.lean) | Common fixed spaces, complementary selectors, preservation and inverse-map construction. Product-range identification currently requires commuting selectors. |
| [Mixed coefficient naturality](../../../Math/RepresentationTheory/Coefficients/MixedCompletenessNaturality.lean), [typed carrier naturality](../../../Math/RepresentationTheory/Constructions/TypedMixedCarrierNaturality.lean) | Actual representation/coefficient transport through statistics-constrained sources. Model callers still owe compatible field maps. |
| [Relation naturality](../../../Math/RepresentationTheory/Relations/LocalRelationNaturality.lean), [derivative interface](../../../Math/RepresentationTheory/Jets/DerivativeInterface.lean) | Relation transport, selected preimages and extraction. No global extension of selected coefficients is inferred. |
| [StandardDensityAction](../../../Math/RepresentationTheory/Lagrangian/StandardDensityAction.lean), [LagrangianModel](../../../Math/RepresentationTheory/Lagrangian/LagrangianModel.lean) | Compatible constant linear field/direction actions, density symmetry and existing full-relation model operations. |
| [Dirac/Weyl convention](../../../Physics/FieldTheory/Mass/Algebra/DiracWeylConvention.lean), [invariant Weyl masses](../../../Physics/FieldTheory/Mass/Algebra/InvariantWeylMass.lean) | Actual all-left mass coefficients and radicals. Signed indices and their antisymmetrizations are distinguished. |
| [Weyl representations](../../../Physics/FieldTheory/Spinor/Weyl/WeylSpinor.lean), [right-Weyl convention adapter](../../../Physics/FieldTheory/Spinor/Weyl/RightWeylChargeConjugation.lean) | Existing left/right actions and an explicit Euclidean four-component bilinear convention. The latter does not by itself prove a universal Minkowski charge-conjugation correspondence. |
| [Vacuum mass protection](../../../Physics/FieldTheory/Yukawa/Mass/VacuumMassProtection.lean), [projected Yukawa families](../../../Physics/FieldTheory/Yukawa/Mass/ProjectedYukawa.lean) | Restriction/evaluation of supplied invariant Yukawa tensors at a retained-invariant vacuum; survival of a proposed light space has explicit conditions. |
| [Light-inheritance boundary](../../../Physics/FieldTheory/Mass/Algebra/LightInheritanceBoundary.lean) | Reusable negative control against inferring light survival from equivariant inclusion and restricted mass agreement. |
| [SU(6) boundary model](../../model-studies/su6-protection/boundary-model.md) | Constructed algebraic selector and field/action maps; five-dimensional mixed-mode admission remains separate. |
| [Lepton-parity SM construction](../../../Physics/StandardModel/Spectrum/Representations/InverseCyclicSMRealization.lean), [Yukawa checks](../../../Physics/StandardModel/Operators/Selection/InverseCyclicSMYukawa.lean) | Different, actual finite mass-radical mechanism with three-generation fields and known coefficient/Yukawa consumers. |

The local pinned mathlib/TauCeti sources determine the APIs. The online
[mathlib subrepresentation documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Subrepresentation.html)
is background navigation, not a dependency-version or completeness premise.
No dependency/toolchain update is planned.

## Primary-Source Comparisons

- A. Angelescu, A. Bally, S. Blasi, F. Goertz, *Minimal SU(6) Gauge-Higgs Grand
  Unification*, Phys. Rev. D 105 (2022) 035026,
  [2104.07366v2 HTML](https://arxiv.org/html/2104.07366v2),
  [publication](https://doi.org/10.1103/PhysRevD.105.035026).
  Reopened Sec. II.2 (5)–(10) and Appendix C for the same boundary/sign
  conventions. Shared joint-action dictionaries preserve the algebraic
  comparison; mixed-mode/spectrum and numerical/empirical boundaries remain.
- The [Lagrangian model source comparison](../lagrangian-model-connections/literature-validation.md)
  and [Euler-naturality comparison](../euler-naturality/literature-validation.md)
  identify the original density/action checks. Dreiner–Haber–Martin
  0812.1594v6 (3.1.1),(3.2.1),(4.3.2)–(4.3.8) and Sardanashvily 1206.2508v1
  Sec. 6 (31),(37) were reopened for the new full-input connection and
  inherited Euler/variation regression scope.

The central [related-literature list](../../proof/RELATED_LITERATURE.md)
contains these sources. Their existing entries now link the implemented
connections and comparisons; no duplicate source identifiers were added.
