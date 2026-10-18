# Conditional Weyl extraction and actual kernel consumers

The user authorized established unformalized mathematics as explicit theorem
parameters after `checkpoint 01`. The [plan](weyl-input-plan.md) fixes the boundary.
The result is a conditional extraction interface, not a completed all-content
multiplicity classifier.

## Proven finite extraction algebra

[CompactWeylExtraction](../../../Math/RepresentationTheory/Characters/CompactWeylExtraction.lean)
defines the root difference `D_a f(w) = f(w)-f(w+a)` and its iterated value at
zero. This is the constant-term operation for multiplication by the one-sided
positive-root denominator. Integer-to-complex casting commutes with extraction.
For A2 roots alpha, beta, alpha+beta, `a2_formula` proves

    CT = f(0) - f(alpha) - f(beta)
         + f(2 alpha + beta) + f(alpha + 2 beta) - f(2 alpha + 2 beta).

The canceling alpha+beta terms are proved algebraically, without a numerical
rank table. Root coordinates remain explicit parameters; their identification
with the SM maximal torus is not supplied by this identity.

## External mathematical input

`Presents rho torus monomial P` states that the actual inverse character on the
specified torus equals the finite integer Laurent presentation P. The inverse
character matches coefficient-Hom counting, rather than vector counting.
`TorusReduction` states that, for every such presentation, the normalized Haar
integral of the inverse character equals its positive-root constant term.

This is an explicit theorem parameter. Its standard sufficient conditions are
a compact connected Lie group, its maximal torus, the actual positive roots
and character lattice in the chosen coordinates, and a continuous finite-
dimensional representation. The Lean structure records the resulting reduction
law; generic group/compactness classes alone do not assert those sufficient
conditions or prove the law. No instance of this input is constructed here.

The source is Peter Woit's [2012 notes](https://www.math.columbia.edu/~woit/LieGroups-2012/weylcharacter.pdf),
section 1, Theorem 1, Theorem 2 and Corollary 1. The one-sided constant-term
law is a derived specialization of character orthogonality and Weyl's formulas,
not a verbatim numbered theorem in those notes. See the plan for locations,
normalization and applicability. The source provides a proof outline and
references for full proofs; it is not an imported Lean implementation.

`coefficient_dimension` combines this parameter with the already proved
`CompactHomDimension.integral_character_mul_eq_finrank`, an explicit joint-
continuity hypothesis and the semantic presentation. It proves that the
integer extracted value equals the dimension of the actual invariant
coefficient space. It assumes neither a numerical kernel dimension nor a rank.

## Conditional SM consequences

[SMWeylExtractionInput](../../../Physics/StandardModel/Operators/SMWeylExtractionInput.lean)
requires, separately:

- a compact representation rho with explicit joint continuity;
- the external `TorusReduction` input for its torus/roots/monomials;
- a finite integer presentation of its actual inverse character;
- a linear equivalence from its invariant coefficients to the existing
  `SMMixedCompactCoefficients.LocalSpace` for the specified p, m, delta.

The last premise is an application comparison, not the Weyl theorem and not
proved by its citation. The previously verified `kernelEquiv` then transports
the extracted dimension to the actual SM kernel. `kernel_dimension_int` and
`kernel_dimension` give integer/natural forms; `multiplicity_nonnegative`
and `multiplicity_le_columns` prove its bounds. `rank_formula` subtracts that
multiplicity from the already proved all-content symbolic column count.
`local_allowed_iff` gives local support exactly when the integer is positive.
Negative extraction values cannot be silently truncated: nonnegativity is
proved before the natural-number interpretation.

These statements retain the actual statistical source and local constraint
matrix. They do not test arbitrary residual invariance: full residual support
is a separate coefficient condition. No CSV value or complete support claim
is introduced.

## Application work at this checkpoint

The subsequent [actual compact extraction result](compact-extraction-results.md)
constructs the comparison, continuity and finite spectral presentation described
below. Its final theorems retain only the Weyl reduction parameter. Concrete
weight recurrences/numerical evaluation and residual classification remain open.


Construct the combined compact gauge/independent-spin representation and its
coefficient comparison to `LocalSpace`, prove joint continuity, and construct
the complete finite torus presentation from species exterior characters and
Higgs weights with the actual root-coordinate dictionary. Only then can the
external reduction input be applied to every actual mixed content without
supplying these extra premises. The existing separate-spin fixed-space theorem
and the source character product are useful, but do not themselves prove
those constructions. This checkpoint closes the conditional consumer, not
these prerequisites or task III as a whole.

Persistent audits: `AuditCompactWeylExtraction` and `AuditSMWeylExtractionInput`.
Their strict axiom checks verify conditional implications; they do not prove
`TorusReduction`, comparison, continuity or presentation premises. No custom
axioms, `sorry`, dependency changes or audit exceptions are used.
