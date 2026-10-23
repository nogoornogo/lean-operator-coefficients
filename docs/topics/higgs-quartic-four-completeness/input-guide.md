# C4 coefficient input

The public module is
[HiggsQuarticFourCompleteness](../../../Physics/FieldTheory/Jets/HiggsQuarticFourCompleteness.lean).
Its final aggregate verification is tracked in [verification](verification.md).
It adds an input certificate; published nonderivative and derivative inputs
retain their existing definitions.

Use `HiggsQuarticFourInput.selected.Coefficient` for coefficients on the
**entire** free Higgs grade (field count 4, derivative count 4). The action
is the actual global covering-SM group times SL(2,C); the relation input is
the full free differential EOM ideal plus the linear IBP range, restricted
by preimage to this grade. The source is not the span of three candidates.

`HiggsQuarticFourCompleteness.equivalence` extracts the values on `(q1,q2,q3)`.
`reconstruction c` constructs the unique admitted coefficient for any
`c : Fin 3 → ℂ`. `normalized i` has value one on candidate i and zero on
the other two. The two inverse laws are `reconstruct` and
`extract_reconstruction`; `coefficient_dimension` gives complex dimension 3.
The public constructors require no moment table, paper count or extension
premise from the caller.

`directEquivalence` supplies the same coordinates for the component-equation
input. `inputEquivalence` and `input_agreement` identify it with the
helper-generated free input without changing evaluation.

The [literature consumers](../../../Physics/FieldTheory/Jets/HiggsQuarticFourLiterature.lean)
provide Murphy coordinates, Li's higher-derivative coordinates and Eboli's
coordinates. Li's value map is `(4c3,c1,c2-c1-c3)` in one-based q notation;
its inverse is `(l2,l3+l2+l1/4,l1/4)`. Eboli's order is `(c2,c3,c1)`.
Use the named `li_extraction` and `eboli_extraction` laws to evaluate their
literal selected representatives. Source locations and specialization
limits remain in [references](references.md).

These are complex algebraic coefficients with independent field/dual
generators. The result does not supply Hermitian real coordinates, local
gauge connections, interacting Higgs/Yukawa EOM, a global invariant extension
to every degree, or a complete SMEFT basis. The dimension statement concerns
admitted invariant coefficients; it does not identify the whole quotient
with the three-candidate image.
