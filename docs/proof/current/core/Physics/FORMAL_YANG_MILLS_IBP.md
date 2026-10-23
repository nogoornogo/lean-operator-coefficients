# Polynomial Scalar And Formal Matrix Yang–Mills Jets

The [polynomial EOM construction](../Math/NONLINEAR_EOM_IBP.md) has two actual
four-dimensional consumers, with signature (+---).

The scalar consumer specifies `box phi + lambda * phi^3`, for any complex
constant `lambda`. The full differential ideal and its quotient are
constructed. Zero-field evaluation detects the surviving unit. The existing
actual Pauli SL(2,ℂ) action fixes the seed, preserves its ideal and descends
to the EOM algebra and linear EOM/IBP source. The retained divergence identity
proves `kinetic = lambda * phi^4` modulo the constructed EOM and actual IBP.
Neither class is asserted nonzero.

The mathematical connection interface takes ordinary linear Leibniz
derivatives that commute on an associative complex algebra. From actual
connection elements it constructs the adjoint covariant derivative and
curvature. Covariant Leibniz, curvature antisymmetry, the curvature commutator
and covariant cyclic Bianchi are proved by associativity and the ordinary
derivative laws. Constant inverse conjugation covariance retains explicit
derivative-constant hypotheses. Curvature/Bianchi covariance is not supplied
as an extra premise.

Entrywise derivatives instantiate this interface on finite matrices over
ordinary polynomial jets of every matrix connection component. The formal
source-free equation is `E_nu = sum_mu s_mu * nabla_mu F_mu,nu`. Its entries
generate the actual nonlinear differential ideal. Both ordinary and covariant
descendants vanish in the quotient. Surjection, exact kernel, finite image
and inverse source/coefficient EOM/IBP interfaces are instantiated. The
zero-field unit survives EOM. A two-by-two constant-jet evaluation detects
curvature one and a nonlinear off-shell EOM component minus two; that
nonzero EOM component vanishes on shell.

Sources:

- [Polynomial scalar EOM](../../../../../Physics/FieldTheory/Jets/Scalar/Inputs/PolynomialScalarEOM.lean).
- [Associative connection identities](../../../../../Math/Algebra/Constructions/FormalConnection.lean).
- [Entrywise matrix derivatives](../../../../../Math/Algebra/Jets/MatrixJetConnection.lean).
- [Formal matrix Yang–Mills consumer](../../../../../Physics/FieldTheory/Jets/Gauge/FormalYangMills.lean).
- [Nonzero polynomial controls](../../../../../Physics/FieldTheory/Jets/Gauge/YangMillsControls.lean).
- [Physical strict audit](../../../../../Physics/FieldTheory/Jets/Scalar/Inputs/Audit/AuditNonlinearGaugeJets.lean).

The [source register](../../../../topics/nonlinear-eom-gauge-jets/references.md)
records Tong's convention guidance; the proofs use `nabla = partial + [A,-]`.
These are formal polynomial models, without a supplied physical covariance,
variational or completeness theorem. No SU(N) real/traceless restriction,
arbitrary local gauge transformation, analytic Maxwell/Yang–Mills equivalence,
matrix-model Lorentz dictionary, general invariant basis/count, amplitude,
matching, RGE or numerical dynamics is certified. IBP remains a linear quotient.
The [verification](../../../../topics/nonlinear-eom-gauge-jets/verification.md)
owns the checked acceptance gates and residual warnings.
