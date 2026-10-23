# Actual Jet Coefficients And Finite-Group Evaluation

## Coefficient Statement

Let `L` be any group and `H` a finite group. On a specified finite-dimensional
complex source `U`, a representation of `L × H` gives commuting local and
residual restrictions. Construct

\[
Q=U/\mathrm{span}_{\mathbb C}\{g u-u:g\in L,\ u\in U\}.
\]

For a finite complex spurion representation `a`, every specified value `s`
has its actual stabilizer `H_s`. There is a proved linear equivalence

\[
\{f\in\mathrm{Hom}_{H_s}(U,\mathbb C):f(g u)=f(u)\}
\simeq \mathrm{Hom}_{H_s}(Q,\mathbb C).
\]

The inverse evaluates a quotient functional at the class of `u`. A basis of
the finite-dimensional dual of `Q` supplies coordinates. Polynomial dual
covariants evaluated at `s` attain every coefficient on the left with total
spurion degree at most `orbitSize(s)-1`, hence at most `|H|-1`. Nonzero and
total-prohibition equivalences follow from this surjectivity. At zero value,
degree zero already attains all coefficients allowed by the full group.

Only `H` is averaged in the inherited finite-group theorem. No finiteness,
compactness, reductivity, averaging or invariant-exactness assumption is made
on `L`. The local coinvariant quotient is the repository construction. It is
not an assumed local invariant dictionary or a new Mathlib identification.

## Actual Sources

The jet interfaces construct the product action before quotienting: `H` acts
on the field components and `L` on derivative directions. Commutation then
follows from restriction of that actual product representation.

| Source | Constructed relations and connection | Checked entry point |
| --- | --- | --- |
| Scalar, fixed `(n,d+1)` | All descendants of the specified constant-coefficient equation symbol `q`, followed by the actual on-shell divergence range. The existing representation equivalence compares this with the off-shell EOM kernel plus IBP range. | `scalarAction`, `scalarSourceEquiv`, `scalar_surjective`, `scalar_card_surjective` |
| Mixed Bose/Fermi, fixed `(n,m,d+1)` | Actual exterior/polynomial grade modulo its divergence range. Stability under direction mixing is proved from covariance on derivative generators. The exterior/symmetric tensor presentation projects onto this quotient. | `mixed_stable`, `mixedAction`, `mixedProjection_surjective`, `mixed_surjective`, `mixed_card_surjective` |
| Four-dimensional massless scalars | The scalar interface with the proved Pauli SL(2,ℂ) dual direction action and invariant symbol `p₀²-p₁²-p₂²-p₃²`, retaining arbitrary finite residual internal action. | `GUT.LorentzSpurionEvaluation.surjective`, `card_surjective`, `pullback_injective` |

Finite component and direction sets give finite-dimensional fixed grades;
quotients and their dual coordinates inherit finiteness. These are discharged
by existing proved instances during construction of the evaluation maps,
not added as source-completeness hypotheses. The scalar generic theorem
requires explicit local invariance of `q`; the Lorentz specialization supplies
the proved wave-symbol invariance. No premise is imported from literature.

`scalar_evaluation_off` and `mixed_evaluation_tensor` evaluate on original
representatives. Both pullbacks are injective because the original projections
are proved onto. `coefficientEquiv_mk` and `coefficientEquiv_symm_apply` give
the two inverse coefficient formulas. The mixed source is off shell and has
no fermionic EOM; its local action here acts on directions. This does not add
a general intrinsic Lorentz-spin action on odd field components.

## Complete Nonzero Derivative Consumer

The existing one-direction source has one odd field `ψ`, one even field `φ`
and grade `(2,1,2)`. Its complete Pauli/IBP quotient is a complex line with

\[
A=[\phi_1\psi_0\psi_1]\ne0,\qquad
[\phi_0\psi_0\psi_2]=-A.
\]

The actual internal group is the two-element group `ℤˣ`. It fixes `ψ` and
multiplies `φ` by its sign character. `action_raw`, `source_sign` and
`quotient_sign` prove that the induced action on the **whole** source and
quotient is that sign, using the already proved complete source span.

A one-dimensional sign spurion has trivial stabilizer at every nonzero
value. Its coordinate polynomial `X` is a proved degree-one dual covariant
on the actual quotient. At value `s`, the induced coefficient sends `A` to
`s` and the second displayed class to `-s`. It is nonzero for every `s≠0`.
At zero value every invariant coefficient vanishes. Every degree-zero
covariant evaluates to zero at every value, making the degree-one control
sharp. Bounded evaluation at degree one is onto all actual coefficients.
The common local/residual bridge is instantiated with an explicit trivial
local group and the same actual quotient. This example is not a 4D basis.

## Sources And Limits

- [Common local/residual connection](../../../Math/RepresentationTheory/LocalSpurionEvaluation.lean).
- [Actual jet consumers](../../../Math/RepresentationTheory/JetSpurionEvaluation.lean).
- [Complete sign-spurion example](../../../Math/Algebra/MixedJetSpurionExample.lean).
- [Lorentz scalar consumer](../../../Physics/FieldTheory/Jets/LorentzSpurionEvaluation.lean).
- [Math strict audit](../../../Math/Algebra/Audit/AuditJetSpurionEvaluation.lean)
  and [physical strict audit](../../../Physics/FieldTheory/Jets/Audit/AuditLorentzSpurionEvaluation.lean).

Spurions are constant and neutral under the local action. Their polynomial
degree is neither an operator mass dimension nor a derivative cutoff.
Arbitrary jet orders remain available, but no global on-shell direct-sum,
minimal degree/dimension classification, general-group saturation, interacting
or Weyl EOM, amplitudes, matching, rates or complete EFT table is proved.
Bibliographic roles and earlier inspected locations stay in the
[source register](references.md); commands and gates are in [verification](verification.md).
