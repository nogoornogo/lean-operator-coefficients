# Compact H: Connection Assessment

## Decision

**Proceed with a bounded compact-continuous qque implementation.** The pinned
TauCeti version already supplies the essential analytic and representation
theoretic inputs. No Lean/mathlib/TauCeti upgrade, new character classification,
or Peter-Weyl foundation is needed for the audited route.

This is an API feasibility result, not yet the compact-H light-source theorem.
The existing non-Abelian qque endpoint still assumes `[Fintype H]`.

## Compiled Connections

The reusable adapter is
[CompactHomDimension](../../../Math/RepresentationTheory/Characters/CompactHomDimension.lean).
It accepts algebraic representations on finite-dimensional complex normed
spaces and the existing `IsJointlyContinuous` predicate.

| Input / interface | Evidence | Outcome |
| --- | --- | --- |
| Algebraic representation to continuous operators | `asContinuous_toRepresentation` | Underlying representation is unchanged |
| Jointly continuous action to operator-valued continuity | `continuous_asContinuous`, using mathlib `continuous_clm_apply` | Proved; no added operator-continuity certificate |
| Compact character integral to algebraic Hom dimension | `integral_character_mul_eq_finrank` | Proved through TauCeti counting and `ContRepresentation.intertwiningMapEquiv` |
| Positive character addition to Hom-dimension addition | `hom_finrank_add` | Proved, with integrability justified by compactness |
| Equivariant surjection to an actual split projection | `SemisimpleSplitting.exists_split` | Proved from semisimplicity of the source only |
| Unitary source supplies the preceding premise | `exists_split_of_unitary` | Proved for arbitrary groups, without Maschke |
| Compact continuous source admits a unitary model | Audit `exists_unitary_model` | Instantiated and axiom-checked TauCeti unitarization |
| Irreducible decomposition on the original carrier | TauCeti `IsUnitary.exists_orthogonal_irreducible_decomposition_of_congr` | Existing theorem compiled and axiom-checked; consumer conversion remains |
| Infinite compact group accepted | Audit `circle_infinite`, `circle_counting` | Circle specialization compiled, with explicit Borel structure |

The compact counting identity is

```text
integral_H chi(rho)(h^-1) * chi(sigma)(h) = dim_C Hom_H(rho, sigma).
```

The inverse character, rather than a conjugated character, is deliberate:
unitarity of the original action is not required by this identity. Using the
linear equivalence of continuous and algebraic intertwiners keeps the current
algebraic quotient/tensor consumers available.

The splitting adapter is
[SemisimpleSplitting](../../../Math/RepresentationTheory/Decomposition/SemisimpleSplitting.lean).
It does **not** assert that the whole group algebra of an infinite compact group
is semisimple. Only the particular source representation needs a complement for
each invariant subspace.

## What Continuity Means Here

`ContRepresentation` by itself packages continuous linear operators; it does
not assert that those operators vary continuously with h. That premise is
supplied by `IsJointlyContinuous` and proved sufficient in the adapter.

The counting API requires `[IsTopologicalGroup H]`, `[CompactSpace H]` and a
Borel measurable structure. Finite-dimensional carriers and action continuity
remain essential inputs. Compactness is not being applied to arbitrary
discontinuous abstract representations.

For the physical consumer, it suffices to supply a continuous residual H action
on the source and a continuous nonzero Q target. The existing target equations
identify the required up/e characters with Q; no new continuity premise on the
ambient gauge group G or the two conjugators is needed by this route. This
consumer-level sufficiency is the proposed implementation interface, not a
theorem proved by this audit.

## Remaining Consumer Work

1. Package residual continuity on the mass radical and monitored weight
   subspaces. Existing `IsJointlyContinuous.comp` and `.subrepresentation` are
   axiom-checked; actual radical/weight instances still need assembly.
2. Supply compatible finite-dimensional topologies on the Q target and the
   opposite-weight algebraic dual, and prove continuity of the latter. A
   continuous dual versus algebraic dual identification must be explicit.
3. Convert compact unitarization/decomposition into the current algebraic
   irreducible quotient and splitting interfaces on the original carriers.
   No change of mass or light subspace may be hidden by changing inner products.
4. Replace finite counting in
   [ResidualLightQuotient](../../../Physics/FieldTheory/Mass/ResidualLightQuotient.lean)
   with `CompactHomDimension.hom_finrank_add`; keep the actual positive target
   and actual opposite-weight dual. Finish the surjection/common-quotient proof.
5. Connect the four monitored weights and the existing
   [ordered invariant pairing](../../../Math/RepresentationTheory/OrderedInvariantPairing.lean).
   Its construction does not need H finite. Prove the compact analogue of
   [FourWeightLightQque](../../../Physics/StandardModel/Operators/FourWeightLightQque.lean)
   and a finite/discrete compatibility control.

Items 1-5 are interface work supported by the audited inputs, not completed
merely because those inputs compile. Highest remaining risk is keeping dual,
subspace and transported norm instances compatible, not a missing compact-group
classification theorem. Do not silently replace the original T-unitarity
assumption by T x H unitarity to avoid this work.

## Scope And Stop

The preferred Haar/Hom-dimension route passed, so the alternative isotypic
projector route was not developed. This audit stops here. A follow-on target
should be the four-weight qque endpoint for compact continuous H, with the
same two actual conjugators and invariant symmetric mass.

Finite-group theorems and their hypotheses are unchanged. No claim of full SM
gauge invariance, Lorentz/Grassmann nonvanishing, a generated coupling, proton
decay, or E6 global topology follows from this audit. The unitarization probe
does not assume H-unitarity on the original representation.
