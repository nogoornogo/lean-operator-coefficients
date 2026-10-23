# Specified Six-Quark Graded Completeness

## Result

[GradedSixQuarkComparison](../../../../../Physics/StandardModel/Operators/BaryonTwo/Coefficients/GradedSixQuarkComparison.lean)
proves a linear equivalence from the independently defined physical `u²d⁴`
model sector to the constructed residual quotient Hom at mixed degree `(6,0)`:

\[
\mathcal C_{u^2d^4}\simeq\mathrm{Hom}_R(Q_{6,0},\mathbb C)
\simeq\mathrm{StatisticsHom}(U,D).
\]

Here `Q` is the separated local-coinvariant/flavor tensor quotient by signed
species exchange, as in [coefficient-space decomposition](../../core/Math/GRADED_OPERATOR_COMPLETENESS.md).
`comparison` gives the second equivalence. Extraction and reconstruction commute
with the old `DeltaBTwoFlavorBridge.sectorHomEquiv`; both inverse laws and total
prohibition/nonzero iff hold. `oneGenerationEquiv` transfers the established
two-probe coordinates for trivial one-generation flavor and residual group.

## Inputs And Conventions

The residual group is arbitrary and `U,D` are independent arbitrary complex
modules with representations `up,down`. No finite-dimensionality, compactness,
self-duality or identification of the two carriers is required.
The content is the specified all-right six-quark exterior bidegree `(2,4)`.
Ordered slots are `u,d,u,d,d,d`. The local group is SM gauge times right Weyl;
its product with the residual group is reassociated from the physical interface.
Hypercharge weights `4,-2` cancel and integer baryon grade `3B` is six.
The [input dictionary](../../../../topics/graded-sector-regressions/interfaces.md)
records the actual-field reordering and the fixed-content support.

## Proof Structure

`field_apply` proves the local/residual action equals the physical slot action.
The empty boson-slot equivalence preserves evaluation. The normalized physical
exterior lift proves compatibility for every species-preserving permutation;
the converse recovers the four typed generators. `orderedEquiv`, combined with
the independent physical-sector restriction/lift and generic quotient completeness,
constructs the new Hom equivalence without assuming the old local-coordinate
classification. The latter supplies a comparison through the same physical input.

The prerequisite `SixQuarkFlavorCoordinates.assemble` uses universal tensor
lifting instead of finite flavor bases. Its pure-tensor formula and both inverses
hold for arbitrary slot modules. Mathlib `irreducible_def` retains proved definition
equations for the large constructed equivalence while preventing costly reduction.

## Verification

[Consumer audit](../../../../../Physics/StandardModel/Operators/BaryonTwo/Coefficients/Audit/AuditGradedSixQuarkComparison.lean)
and [inverse audit](../../../../../Physics/StandardModel/Operators/BaryonTwo/Coefficients/Audit/AuditSixQuarkArbitraryFlavor.lean)
check the declarations transitively, including the definition equation. Only
`propext`, `Classical.choice` and `Quot.sound` are permitted. Commands and
compatibility verification are recorded in the [topic results](../../../../topics/graded-sector-regressions/results.md).

## Boundaries And References

The residual target has 25 local entries constrained by typed flavor exchange;
it is not 25 free coefficients or generally two-dimensional. There is no new
claim about the printed ten-seed span, other six-quark chiralities, derivatives,
all-degree decision algorithms, matching or rates. This is an internal connection
theorem, not a new literature certificate. See [Physics assumptions](../../inputs/Physics/ASSUMPTIONS.md)
and the [separate Li certificate](LI_SIX_QUARK_BASIS.md).
