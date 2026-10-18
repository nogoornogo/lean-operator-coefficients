# Full diagonal Majorana stabilizer: results and boundaries

## Exact endpoint

For any finite index set `I` and specified `c : I → ℂ`, the actual unitary
stabilizer of the complex bilinear form `∑ i, c i * x i * y i` is group-equivalent
to

```
(product over zero-mass fibers of U(fiber)) ×
(product over nonzero absolute-value fibers of O(fiber, ℝ)).
```

The factors are indexed by the finite image of `i ↦ ‖c i‖`. They act on the
actual subtype fibers, not on externally supplied multiplicity dimensions.
`MajoranaUnitaryClassification.classification` and
`FlavorMajoranaUnitary.classification` include verified inverses. No positivity,
partition, phase-normalizer or literature premise is imposed on `c`.

## Construction

1. [UnitaryDiagonalCongruence](../../../Math/LinearAlgebra/UnitaryDiagonalCongruence.lean)
   constructs the full subgroup and proves its exact entry equations.
   `bilinear_iff` connects transpose congruence to preservation of the complex
   bilinear form. `no_mixing` separates unequal absolute values.
2. [UnitaryMajoranaBlocks](../../../Math/LinearAlgebra/UnitaryMajoranaBlocks.lean)
   proves an explicit product equivalence for an arbitrary finite dependent
   family of blocks with distinct squared absolute values. Its assembling map
   is bijective; the inverse is block restriction. No block size must be positive.
3. [MajoranaPhaseNormalization](../../../Math/LinearAlgebra/MajoranaPhaseNormalization.lean)
   proves existence of a Circle phase `p` satisfying `c*p² = ‖c‖`, choosing `1`
   at zero. Existence uses the proved algebraic closedness of ℂ, not an added
   axiom. The diagonal phase matrix is unitary; conjugation transports the
   actual stabilizer through `normalizationEquiv`. Its orientation and inverse
   are checked by `conjugate_preserves` and `undo_congruence`.
4. [MajoranaUnitaryClassification](../../../Math/LinearAlgebra/MajoranaUnitaryClassification.lean)
   supplies the finite mass image, its fibers and inverse reindexing. It
   composes normalization, reindexing, block decomposition and zero/nonzero
   factor equivalences into `classification`. Real orthogonal matrices embed
   by complexification; their inverse coordinates are real parts.
5. [FlavorMajoranaUnitary](../../../Physics/FieldTheory/Mass/FlavorMajoranaUnitary.lean)
   uses the full unitary defining action and the already existing
   `FlavorMajoranaDiagonal.form`. `form_matrix` and `subgroup_eq` prove that
   this is the same form and same stabilizer, not a new assumed model interface.

## Residual Hom

Both classification namespaces provide `residualHomEquiv` and
`residual_nonzero_iff`. Supplied representations on the actual stabilizer are
transported to product coordinates using the inverse group equivalence.
Underlying linear maps are unchanged. The consumer modules may have arbitrary
dimension; no compactness or continuity hypothesis is added to this algebraic
transport. Existing operator consumers still require their species and
gauge/Lorentz input identifications; no automatic physical matching is asserted.

## Controls and scope

- Empty index sets and empty blocks are supported throughout.
- The zero form has all of U(I); a constant nonzero complex diagonal form has
  O(I, ℝ), not merely independent signs.
- Positive distinct masses prohibit mixed entries; repeated positive masses
  admit orthogonal mixing.
- `opposite_phase_mixing` exhibits mixing of coefficients `1` and `-1` with
  entries involving `Complex.I`. Equal absolute values, not equal complex
  coefficients, define the blocks.

This is a full classification for **specified diagonal forms** inside the
entire unitary group. It is not a Takagi theorem diagonalizing arbitrary
nondiagonal forms, a classification of simultaneous Yukawa orbits, a preferred
vacuum theorem, or a derivation of observed flavor data. Group equivalences
here are algebraic; no topological group equivalence is claimed. Phase choices
need not vary continuously with coefficients.

These are this topic's boundaries, not missing premises in the later
[Takagi existence extension](../majorana-congruence-interface/existence.md).
That extension proves diagonalization for arbitrary finite symmetric matrices
and transports the present classification to their actual stabilizers.
Simultaneous Yukawa classification remains outside both topics.

## Verification

Persistent audits:

- [Math audit](../../../Math/LinearAlgebra/Audit/AuditUnitaryDiagonalCongruence.lean):
  32 strict transitive checks.
- [Physics audit](../../../Physics/FieldTheory/Yukawa/Audit/AuditFlavorStabilizer.lean):
  60 checks including six full-unitary consumer declarations.

Only `propext`, `Classical.choice`, `Quot.sound` are allowed. No custom axioms,
`sorry`, external computational premise or resource-limit increase was used.
Intermediate elaboration and type-inference timeouts were corrected by explicit
typed transports without changing resource limits. The overview records final
build, layout, link and integration results.
