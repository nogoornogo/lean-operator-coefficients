# Code And Literature Evidence

Inspection date: stage 01. Source/API audit, not an elaborated prototype or
fresh build. LSP MCP was unavailable in this session.

## Pinned Environment

The [toolchain](../../../lean-toolchain), [Lake file](../../../lakefile.lean)
and [manifest](../../../lake-manifest.json) specify Lean `v4.34.0-rc2`,
mathlib `30a58f795ae8c95b8299fe3c9ded1e6498a9e9fe` and TauCeti
`355c248fa848acd70c2a4b412ca5f53d37b0402a`.
Physlib, Physlibalpha and LeanPool are not direct dependencies of this build.
No package addition, upgrade, port or copied external proof is proposed.

## Existing APIs And Gaps

| Source | Checked API / use | Boundary |
| --- | --- | --- |
| [InvariantMassData](../../../Physics/FieldTheory/Mass/InvariantMassData.lean) | `SymmetricMass`, `restrict` | T invariance is not S invariance |
| [SymmetricMassIndex](../../../Physics/FieldTheory/Mass/SymmetricMassIndex.lean) | `toIntertwiningMap`, `radical`, `mem_radical`, `radical_dual_character_eq` | Kernel stability/index preservation are generic; same-form restriction adapter remains |
| [PhysicalTorus](../../../Physics/StandardModel/Gauge/PhysicalTorus.lean) | `gaugeHom`, `toTorus`, `toTorus_surjective`, `weightCharacter_toTorus` | Compatibility must use these actual maps |
| [CompactExplicitSMTensor](../../../Physics/StandardModel/Gauge/CompactExplicitSMTensor.lean) | `Decomposition`, `residual_agrees` | `quark0/quark3/up8/electron14` use entire torus sectors |
| [FourWeightLightQque](../../../Physics/StandardModel/Operators/FourWeightLightQque.lean) | `characters_compatible` | Equates target characters; does not classify SM components |
| [ProductFactorization](../../../Math/RepresentationTheory/Decomposition/ProductFactorization.lean) | `MultiplicitySpace`, `multiplicityRepresentation`, `multiplicityEvaluationLinear_injective` | Injectivity uses algebraically closed field and finite-dimensional irreducible first factor |
| Same file | `multiplicityEvaluationEquiv` | Requires irreducibility of product representation; not applicable to arbitrary whole radical |
| [CompactProductFactorization](../../../Math/RepresentationTheory/Decomposition/CompactProductFactorization.lean) | `multiplicityRange_jointlyContinuous` | Continuity on evaluation-image model; transport to chosen carrier remains |
| [CompactPositiveCharacterQuotient](../../../Math/RepresentationTheory/Characters/CompactPositiveCharacterQuotient.lean) | `exists_surjective_of_character_add_of_nonzero` | Continuous finite-dimensional compact-H reps; no SM classification |
| [CompactResidualLightQuotient](../../../Physics/FieldTheory/Mass/CompactResidualLightQuotient.lean) | Existing positivity/splitting pattern | Output is on torus sectors, not SM multiplicity spaces |
| [SemisimpleSplitting](../../../Math/RepresentationTheory/Decomposition/SemisimpleSplitting.lean) | `exists_split` | Requires semisimplicity, to be derived from compact continuity |
| [SplitRepresentationProjection](../../../Math/RepresentationTheory/Decomposition/SplitRepresentationProjection.lean) | `dualMap`, `dualEquiv`, `dual_comp`, `bidualEquiv`, `Split.dual` | Duality reverses arrows; split projections supply right-handed inclusions |
| [QqueSpinorExterior](../../../Physics/StandardModel/Operators/QqueSpinorExterior.lean) | `exists_on_fields`, `HasNonzeroAlternation.exists_exterior` | Accepts general multiplicity reps/common splits, not tied to entire weight spaces |
| [CompactLightExteriorQque](../../../Physics/StandardModel/Operators/CompactLightExteriorQque.lean) | Existing source endpoint | Still explicitly takes old `Decomposition`; preserve it |

The inspected `Physics/StandardModel` sources do not supply concrete gauge
irreducibility instances for Q/up/e. Reusable tools include
[basis-coordinate irreducibility](../../../Math/RepresentationTheory/Decomposition/BasisIrreducibility.lean)
and [product irreducibility](../../../Math/RepresentationTheory/Decomposition/ProductIrreducibility.lean).
[SU5 matter irreducibility](../../../GUT/SU5/Representations/MatterIrreducibility.lean)
illustrates technique, not irreducibility after SM restriction. Physics must
not import GUT to obtain these prerequisites.

Pinned TauCeti's
`TauCeti/RepresentationTheory/Compact/Character/IsotypicProjection.lean`
provides `ContRepresentation.isotypicProjector`, `range_isotypicProjector`
and `isotypicProjector_idempotent`. The range/idempotence results require
unitary ambient action, compact continuous group data and an irreducible
selected type. They optionally supply isotypic projections, not an automatic
SM-source bridge. H-commutation and transport from unitary models remain.
The recommended evaluation-image route need not redevelop this theory.

[GaugeTorusTrace](../../../Physics/StandardModel/Spectrum/GaugeTorusTrace.lean)
computes basic physical-torus traces, not the complete extraction of
H-valued SM multiplicity indices from an S x H character identity (FSM-5).

The [actual SU6 mass](../../../GUT/SU6/SelectionRules/Models/StandardSMUVMass.lean)
and [branching dossier](../../proof/current/inputs/GUT/SM_BRANCHING.md) supply a nonzero
SM-invariant mass with identified light radical and neutral residual action.
They are positive-control material, not an arbitrary non-Abelian source
result or ready instance of the new interface.

## Primary Literature

1. Alonso, Chang, Jenkins, Manohar and Shotwell,
   [arXiv:1405.0486v2](https://arxiv.org/html/1405.0486v2), equations (1), (9).
   This previously used reference fixes qque gauge/spinor contraction,
   right-handed u/e conventions and Q-slot exchange. It supports the existing
   exterior construction's interpretation, not a lift from torus support to
   SM multiplets or nonzero Wilson coefficients for arbitrary sources.
2. Etingof et al.,
   [Introduction to Representation Theory](https://math.mit.edu/~etingof/replect.pdf),
   Proposition 2.2 and Theorem 2.5, printed pages 23-24.
   Semisimple multiplicity subspaces and the density theorem underlie local
   evaluation injectivity. They do not identify physical SM irreducibles
   within an arbitrary weight sector.
3. Etingof, MIT 18.755 Spring 2024,
   [Lecture 9, section 35](https://ocw.mit.edu/courses/18-755-lie-groups-and-lie-algebras-ii-spring-2024/mit18_755_s24_lec09.pdf),
   Proposition 35.1, Corollary 35.2 and Theorem 35.4.
   Invariant inner products, complete reducibility and coefficient orthogonality
   give the standard route to splitting/species extraction. These notes cover
   compact Lie groups; arbitrary compact H is not restricted to Lie groups
   here. Pinned compact-H APIs provide the formal assumptions actually used.

These references justify a strategy, not a new literature axiom or an already
checked bridge. No source text or implementation was copied into Lean.
No general ambient-group classification, infinite-dimensional Peter-Weyl
development or E6 topology is required by this plan.
