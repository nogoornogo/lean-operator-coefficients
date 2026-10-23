# Polynomial Differential Equations And Linear IBP Descent

For a commutative complex algebra `A`, a family of ordinary derivations `D_i`
and an arbitrary seed set `R`, `Math.DifferentialEquation.ideal` is the ideal
spanned by every iterated derivative word of each seed. No linearity,
homogeneity, finite seed set or derivative commutation is assumed.
`stable` and `minimal` prove that this is exactly the least derivative-stable
ideal containing the seeds.

The quotient projection is surjective with the exact ideal kernel.
`derivative` uses mathlib's `Derivation.liftOfSurjective` after proving kernel
stability. It satisfies the representative formula and Leibniz law. If the
ordinary derivatives commute, so do their quotient derivatives.

Define `Div` as the range of the actual finitely supported-current divergence.
`shell_ibp_map` identifies the on-shell range with the projection image of
the off-shell range. `sourceEquiv` and `coefficientEquiv` give inverse linear
comparisons between `A/(J + Div)` and `(A/J)/Div`, and their linear coefficient
spaces. The outer quotients are vector spaces; the construction does not
ideal-close IBP or multiply integrated classes.

Finite-dimensional source subspaces have finite-dimensional quotient images.
Nonlinear relations can mix field numbers, and no global direct-sum grading
or normal form is asserted. `scalar_linear_recovery` recovers the retained
linear ideal from the linear forms of its relation module.

Generic algebra/IBP transport requires explicit seed/ideal stability and
derivative covariance. These hypotheses are visible in the theorem statements.
The scalar physical consumer proves its own Lorentz inputs.

Sources:

- [Differential ideal, quotient, evaluations and transport](../../../../../Math/Algebra/Jets/DifferentialEquationIdeal.lean).
- [Actual divergence and inverse comparisons](../../../../../Math/RepresentationTheory/Jets/NonlinearJetIBP.lean).
- [Linear recovery](../../../../../Math/Algebra/Jets/NonlinearJetLinearRecovery.lean).
- [Strict mathematical audit](../../../../../Math/Algebra/Jets/Audit/AuditNonlinearGaugeJets.lean).

The [topic result](../../../../topics/nonlinear-eom-gauge-jets/results.md)
and [verification](../../../../topics/nonlinear-eom-gauge-jets/verification.md)
record the scalar and matrix consumers, assumptions and checked boundary.
No literature completeness or analytic equation premise is used.
