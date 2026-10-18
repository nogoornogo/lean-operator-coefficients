# Binary mixed contents using mathlib's graded exterior product

The first mixed-source adapter is proved uniformly in both exterior degrees.
For any two distinct species s,t and any supplied group representations,

    exterior^n V_s tensor exterior^k V_t
      equiv Source(r, append(s repeated n, t repeated k)).

The equivariance is for the full supplied group. It does not require trivial
residual actions, single chirality or a replacement by one diagonal SU2.
The result covers exactly two distinct species (either degree can be zero),
not a decomposition of all finite-species contents.

## Mathematics and actual statistical source

[BinaryExteriorProduct](../../../Math/LinearAlgebra/BinaryExteriorProduct.lean)
uses the pinned mathlib `ExteriorAlgebra.prodEquivTensor`. The homogeneous
inclusions into the two exterior algebras are injective; flatness over a field
makes their tensor map injective. Composing with the inverse graded-product
equivalence proves injectivity of the mixed wedge map. `map_pure` identifies
its value with the ordered concatenation of the two included wedges, with
no extra factorial or unsigned-commutation premise. The construction works
over any field; the statistical-source adapter uses the project's ℂ scalars.

[BinaryPatternExterior](../../../Math/RepresentationTheory/BinaryPatternExterior.lean)
includes the two field modules in the full finite-species module. Distinctness
of s,t proves injectivity. Projection to the existing statistical image yields
`forward`. `inclusion_forward` proves that projection preserves this entire
image, and `forward_surjective` uses the ordered-tensor spanning property and
explicit left/right reconstruction. `linearEquiv` therefore identifies the
actual image, rather than defining a new mixed-source surrogate.

`raw_action` and `equiv` prove full group equivariance. `dimension` gives

    finrank Source = choose(finrank V_s,n) * choose(finrank V_t,k).

`character` gives the product of the two exterior characters. For diagonal
bases, `character_diagonal` identifies the actual source character with the
product of the two coefficients of the finite generating products
`product_i (1 + eigenvalue_i * X)`. These are degree-uniform symbolic proofs;
no numerical case enumeration supplies a premise. They are character
formulas, not singlet extraction or A2 invariant-counting formulas.

[BinaryPatternCoefficient](../../../Math/RepresentationTheory/BinaryPatternCoefficient.lean)
adds an arbitrary supplied spectator representation. `withSpectator` preserves
the full action; `equiv` identifies supported invariant coefficients on the
original full exterior carrier with invariant coefficients on the two-factor
exterior tensor and spectator. Thus the coefficient-level interface retains
nontrivial residual actions without classifying their invariants.

## Standard Model connection

[SMBinaryContentRanks](../../../Physics/StandardModel/Operators/SMBinaryContentRanks.lean)
instantiates this theorem for any distinct pair among all ten signed species,
with the actual gauge, paired Weyl and supplied residual flavor action.
Flavor count remains three. `sourceEquiv` preserves that entire action;
`source_dimension` and `carrier_dimension` give

    choose(d_s,n) * choose(d_t,k) * (m+1)

columns in the actual source/Higgs constituent carrier. `charge` proves the
additive hypercharge formula. `rank_add_nullity` connects this column count
to the existing actual finite local constraints. `charged_rank` and `odd_rank`
prove full rank in the independently forbidden cases. Neutral nullity is not
assumed zero or assigned a computed value.

`reordered_source_dimension` uses the existing exact multiplicity equivalence
to cover other orderings with the same content. Its count equality is an
indexing condition, not a supplied invariant-dimension or spanning premise.
The CSV and constant-content evaluator are unchanged.

## Remaining obligations

The binary adapter is complete. The subsequent
[finite-tree result](iterated-mixed-results.md) now proves multidegree-compatible
iteration and actual-image identification for canonical finite species trees.
The proved dictionary adapter now connects that result to all existing signed
SM contents, including symbolic dimension and column formulas; invariant
counting remains a separate interface.

The independent left/right coefficient comparison was subsequently proved
for arbitrary contents in the [mixed-chirality result](mixed-chirality-results.md).
The mixed-character-to-invariant-dimension connection still needs its compact
counting adapter and SU3 A2 extraction; the character product theorem does not
supply those counting statements. No residual q/l classification,
572-assignment enumeration, new dependency or physical matching assertion is
introduced. See the [continuation plan](mixed-mathlib-plan.md) and
[verification](verification.md).
