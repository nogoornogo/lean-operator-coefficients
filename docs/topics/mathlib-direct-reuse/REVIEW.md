# Library Reuse Review

Reviewed at stage 01 against project base `checkpoint 01`, mathlib
`30a58f795ae8c95b8299fe3c9ded1e6498a9e9fe` and TauCeti
`355c248fa848acd70c2a4b412ca5f53d37b0402a`. Dependency revisions are unchanged.

## Findings And Actions

| Local module | Existing dependency API / finding | Action |
| --- | --- | --- |
| [BasedLieComparison](../../../Math/LieAlgebras/BasedLieComparison.lean) | mathlib `LieAlgebra.Basis.prodEquivLeft` already requires only target simplicity. The source's unused section variable does not occur in its elaborated type. | Replace the adapted kernel/projection proof and local construction with direct helper calls. Preserve public wrappers and generator equations. |
| [RootSpaceDimension](../../../Math/LieAlgebras/RootSpaceDimension.lean) | TauCeti `finrank_eq_finrank_cartan_add_card_root` has the same field, Killing, finiteness, Cartan and triangularizability hypotheses. | Replace the independent dimension proof with the public theorem plus conversion from `Finset.card` to `Nat.card`. No new package/revision. |
| [SerreMatrixBasis](../../../Math/LieAlgebras/SerreMatrixBasis.lean) | Already imports `IsSerreSystem` and the integral matrix cast map; local code builds the generated carrier and a mathlib `LieAlgebra.Basis` under explicit independence/nondegeneracy inputs. | Retain the connecting construction. The reviewed APIs did not supply this exact wrapper. No copied proof identified in this review. |
| [PinnedGeckBasis](../../../Math/LieAlgebras/PinnedGeckBasis.lean) | Already reuses the Geck basis, reindexing and TauCeti base-change APIs; its dimension result consumes `RootSpaceDimension`. | Retain the numbering/compatibility adapter; it now benefits from the public dimension theorem through that wrapper. |

The second finding is semantic duplication, not evidence that the local proof
was copied. The first correction supersedes the old explanation that copying
was necessary to remove a source-simplicity premise.

## Horizontal Checks And Limits

- Searched all project Lean and tool source text for whole-word provenance
  indicators: adapted, ported, copied, copyright, license, SPDX, taken from,
  and related phrases. `BasedLieComparison` was the only explicit external
  proof-adaptation/license notice found. Other occurrences of "copied" described
  mathematical copies of representation spaces, not source-code ports.
- Searched `import all` and internal-helper/reimplementation indicators.
  `BasedLieComparison` was the only project Lean `import all` use found.
- Compared 517 project Lean files with 13,809 pinned mathlib/TauCeti Lean files.
  The heuristic removed comments, normalized whitespace, ignored imports and
  short lines, and compared windows of six retained lines (each at least 20
  characters). No exact matching windows were found after the projection edit.
- Inspected the three adjacent E6 comparison helpers above and searched the
  pinned Lie/root-system APIs by statement/name. That semantic check found the
  dimension theorem despite the absence of matching source text.

This is not an exhaustive provenance or license audit. Comment stripping and
text windows are heuristics; renamed, reformulated and shorter adaptations can
escape them. "No matching window" does not imply originality, absence of other
reusable library results, or permission to remove existing attribution.

## Remaining Boundary

The comparison still uses mathlib's internal API through `import all`; a pin
upgrade needs a compatibility check. Its public equal-dimension convenience
interface may be useful upstream, but the projection argument and dimension
formula are not missing upstream mathematics.

At the `checkpoint 02` refactoring checkpoint, the original Apache-2.0 notice and
license text were retained. That work removed maintained proof duplication,
not attribution history, and did not choose a repository-wide license.
The user subsequently approved [local notice removal](../../architecture/DISTRIBUTION.md).
Historical dossiers still describe their original checkpoints.
