# Results And Successful Stop

All statements in the [contract](plan.md) are proved. The optional adapters
retain the generic specified-EOM interface and the existing dependency pins.

## Evolutionary Jets And Actual Substitution

[Math.JetFirstVariation](../../../Math/Algebra/JetFirstVariation.lean) prolongs
arbitrary polynomial component variations to every jet in four commuting
ordinary directions. The resulting derivation commutes with each total
derivative on every polynomial. An actual polynomial substitution sends each
jet to itself plus epsilon times its prolonged variation. Its degree-zero
coefficient is the input and its degree-one coefficient is the derivation.
Higher coefficients are retained; no finite invertibility or flow is asserted.

## Scalar Interaction

[ScalarFirstVariation](../../../Physics/FieldTheory/Jets/ScalarFirstVariation.lean)
uses signature (+---), arbitrary complex coupling and arbitrary polynomial eta:

`L = kinetic/2 - lambda*phi^4/4`

`delta L = -eta*(box phi + lambda*phi^3) + sum_i D_i(s_i*eta*D_i phi)`.

The identity holds before quotienting. It descends through ordinary IBP and
vanishes in the existing full EOM/IBP source. The negative Euler coefficient
generates exactly the existing differential EOM ideal, including descendants.
The actual substituted Lagrangian has this degree-one coefficient.

## Formal Matrix Yang–Mills

[ConnectionFirstVariation](../../../Math/Algebra/ConnectionFirstVariation.lean)
derives curvature variation and trace IBP decomposition for commuting scalar
derivations on a commutative complex algebra and finite matrix indices.
[YangMillsFirstVariation](../../../Physics/FieldTheory/Jets/YangMillsFirstVariation.lean)
instantiates those identities on the actual full connection jet polynomial algebra:

`L = -(1/4)*sum_i,j s_i*s_j*trace(F_ij*F_ij)`

`delta F_ij = nabla_i eta_j - nabla_j eta_i`

`delta L = sum_j s_j*trace(eta_j*E_j) + sum_i D_i current_i`

`current_i = -sum_j s_i*s_j*trace(eta_j*F_ij)`.

For variation of component `A_j,a,b`, the bulk coefficient is `s_j*E_j,b,a`.
Component extraction proves the transpose and sign explicitly. These Euler
coefficients generate exactly the existing differential EOM ideal. The first
variation descends through actual ordinary IBP and vanishes in the full
EOM/IBP source; its substitution coefficient is also proved directly.

## Boundary

These are formal algebraic density identities. No integration, boundary
condition, analytic variational principle, real/traceless SU(N) restriction,
quantum equivalence, scattering statement or higher-order field-redefinition
equivalence is proved. Literature provides convention and scope guidance,
not an assumed first-variation identity. See [sources](references.md) and
[verification](verification.md). The verified child stops unmerged.
