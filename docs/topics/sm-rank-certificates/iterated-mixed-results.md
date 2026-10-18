# Finite-tree iteration of selected exterior sources

The mathematical iteration is proved for arbitrary finite content trees and
symbolic degrees. The result constructs an equivariant isomorphism from the
iterated tensor product of the leaf exterior powers to the actual
`PatternExteriorSource` for the tree's concatenated content. There is no
supplied decomposition, span, rank or multiplicity premise.

The canonical tree labels are now connected to finite indexed field dictionaries
and the existing ten signed SM species. Every ordered SM content has a proved
full-action decomposition and a symbolic source/carrier dimension formula.
Invariant multiplicity extraction and complete support classification remain
open; dimension and character products do not determine the invariant subspace.

## Disjoint-family induction step

[SumPatternExterior](../../../Math/RepresentationTheory/SumPatternExterior.lean)
splits two entire finite species families, each with an arbitrary selected
pattern p or q. For their sum family and concatenated pattern it constructs

    Source(r,p) tensor Source(t,q)
      equiv Source(sumFields(r,t), append(inl p,inr q)).

Both sides are the repository's actual statistical images. Injectivity uses
the existing graded binary exterior-product map, tensor injectivity over a
field, and the product-to-sum field equivalence. `raw_pure` identifies pure
selected wedges with their ordered concatenation. Source tensor extensionality
then proves that projection preserves the whole image. Explicit left/right
reconstruction and the surjective ordered-source map prove surjectivity.
`values_action` and `equiv` retain the complete supplied group action.

Disjointness comes from the sum-species tags; no condition identifying common
irreducibles is substituted for actual statistics. One family may already
contain arbitrarily many species, so this step can be iterated.

## Uniform finite-tree construction

[ExteriorContentTree](../../../Math/RepresentationTheory/ExteriorContentTree.lean)
provides:

- `Leaf`: a field carrier, its additive/module structures, supplied full
  representation and exterior degree;
- `Content`: either a leaf or a binary node;
- `Species`, `Fields`, `fields`, `degree` and `pattern`: the canonical finite
  species family and the actual concatenated content;
- `factor`: the recursively constructed tensor of leaf exterior representations;
- `decomposition`: its unconditional equivalence with the actual statistical
  representation, proved recursively from constant and sum-family results.

The construction is not limited to three species or a bounded degree list.
`nodeTransport` explicitly aligns the canonical node and sum-family source
instances; it changes no vectors or group action.

`FiniteLeaves` asserts only that each supplied field module is finite
dimensional. Under this dimension hypothesis, `source_dimension` gives the
recursive product of `choose(finrank field, exterior degree)` over leaves.
`source_character` gives the corresponding product of actual exterior
characters. It is a character product, not a singlet-counting theorem.
Neither finiteness nor an invariant multiplicity is assumed for `decomposition`.

`withSpectator` and `coefficientEquiv` retain an arbitrary supplied spectator
and transport supported invariant coefficients on the original full exterior
carrier to coefficients on the iterated tensor. The group is arbitrary;
gauge, Weyl and residual actions can be supplied without being trivialized.

## Species relabeling and the actual SM dictionary

[PatternSpeciesEquiv](../../../Math/RepresentationTheory/PatternSpeciesEquiv.lean)
transports actual statistical images through a species bijection and supplied
equivariant field identifications. `total_single` proves the coordinate action;
`raw_pure` and `forward_pure` identify pure selected wedges. Source spanning,
exterior injectivity and reconstruction through inverse field maps prove
injectivity and surjectivity. `equiv` retains the full group action.

[IndexedExteriorContent](../../../Math/RepresentationTheory/IndexedExteriorContent.lean)
constructs a tree with one leaf for every index in `Fin (k+1)`, including leaves
of degree zero. `labels` is a constructed bijection and `fieldEquiv` is a proved
identification of each field representation. Neither is an existence premise.
`pattern_counts` proves each species occurs precisely its supplied leaf degree.
`degree_of_counts` derives the total length from those counts.
`wordDecomposition` then identifies the tree tensor with any ordered word of
the same content using `PatternMultiplicityEquiv`. It covers arbitrary
nonempty finite species dictionaries and arbitrary degrees; the word itself
can be empty. `word_dimension` and `word_character` give finite products over
the original indices. `wordWithSpectator` and `wordCoefficientEquiv` transport
spectators and supported coefficients on the original exterior carrier.

[SMIteratedContent](../../../Physics/StandardModel/Operators/SMIteratedContent.lean)
instantiates the construction at the existing `Fin 10` signed species. Its
leaf fields and representations are exactly `DeltaLOneSignedFields.field`,
with the fixed three-generation carriers and arbitrary supplied residual
flavor representations. Gauge, paired Weyl and residual actions all remain.
For an arbitrary word p, let c_s count its occurrences of species s and let
D_s be the existing field dimensions `[36,18,18,12,6,36,18,18,12,6]`.
The proved formulas are

    dim Source(p) = product_s choose(D_s, c_s)
    columns(p,m) = dim Source(p) * (m+1)
    character Source(p)(g) = product_s character exterior^(c_s)(field_s)(g).

`sourceEquiv` is the full-group representation equivalence;
`source_dimension` and `carrier_dimension` apply to the actual existing source
and local matrix carrier. `coefficientEquiv` retains an arbitrary full-group
spectator and coefficients supported on p. `rank_add_nullity` gives the actual
constraint rank plus kernel dimension as the proved column count.
`charged_rank` and `odd_rank` express existing full-rank results with this
symbolic column formula for arbitrary content, without matrix enumeration.

## Application boundary and remaining work

Finite-tree iteration and the existing ten-species dictionary adapter are
complete, including arbitrary original words, dimensions, character products
and supported coefficient transport. Each species occurs in one leaf; repeated
occurrences are handled by its exterior degree, preserving statistics.
No neutral kernel dimension or new CSV entry follows from the column formula.

A2 invariant extraction, mixed-character counting and residual q/l
classification remain independent. The already proved mixed-chirality
comparison is unchanged. No dependencies, pins, custom axioms, literature
premises or physical matching assertions were added. Persistent audits are
`AuditIteratedExterior`, `AuditPatternSpeciesEquiv` and `AuditSMIteratedContent`.
See the [iteration plan](iterated-mixed-plan.md) and [verification](verification.md).
