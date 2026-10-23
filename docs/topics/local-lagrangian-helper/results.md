# Generated EOM And Boundary Inputs

The optional helper accepts finite complex local polynomial expressions with
mixed odd/even field components and arbitrary finite words of ordinary total
derivatives. It reuses the actual exterior/polynomial jet algebra. Existing
published inputs and dependency pins are preserved.

## Proved Construction

`LocalPolynomial.Expr` evaluates constants, field jets, sums and products in
the actual mixed algebra. Word evaluation agrees with the existing total
derivatives; the expression derivative has the corresponding evaluation.
Parity and the required sliding signs follow from exterior multiplication.

`linearize` constructs variation-jet coefficients by the even Leibniz rule,
moving variation components to the left with actual parity signs.
`VariationalIBP.adjoint` and `current` repeatedly move ordinary derivatives
from those components to their coefficients, preserving multiplication order.
For every expression and every parity-preserving variation, the compiler proves

$$
\delta L=\sum_s\eta_s E_s(L)+\sum_i D_i J_i.
$$

The Euler family has finite support. Currents are explicit finite-support data.
Euler construction respects sums, scalar multiples and subtraction. The
syntax-directed variation agrees with any compatible actual evolutionary
derivation. In four-dimensional bosonic jets it agrees with the existing
polynomial derivation and actual epsilon-substitution coefficient.

The generated mixed equations use the least complex submodule containing all
Euler seeds and closed under left/right multiplication and total derivatives.
Minimality is proved. Its commutative specialization equals the old full
differential EOM ideal viewed linearly. IBP adds only the actual linear
divergence range. The first variation has the proved bulk class modulo IBP
and is zero in the full generated EOM/IBP source.

Both routes return the existing common input operations; extraction is
unchanged quotient evaluation. No homogeneous on-shell decomposition is
assumed and no coefficient enumeration/solution algorithm is supplied.

## Usage Controls

The scalar controls generate the equation from `-g*phi^6/6`, the derivative
interaction `phi^2*(D_0 phi)^2`, and `(D_0 D_0 phi)^2/2`. Their Euler
coefficients are, respectively, `-g*phi^5`,
`-2*phi*(D_0 phi)^2 - 2*phi^2*D_0 D_0 phi`, and `D_0^4 phi`.
Zero and a total derivative have zero coefficients. A potential alone is
accepted without a kinetic or regularity hypothesis.

The mixed Yukawa example verifies both odd signs against actual left exterior
contractions, as well as odd reordering and square-zero cancellation. Its
factory needs only the interaction expression. These labels alone do not
assert a physical gauge/Lorentz spinor dictionary.

The actual Lorentz scalar consumer reuses the existing four-direction action
and signature (+---). Its kinetic density plus `-g*phi^6/6` gives
`-(box phi + g*phi^5)`. Generated ideal and divergence stability are proved
once; the consumer's caller supplies only g. A requested generic action still
needs its stability certificate. Arbitrary interaction invariance is not inferred.

## Boundary And Usability Evidence

See [input guide](input-guide.md), [implementation dossier](../../proof/current/inputs/Math/interfaces/local-lagrangian-helper.md)
and [verification](verification.md). The compiled examples show interaction-only
edits and no caller-supplied EOM/first-variation formula. They do not establish
that every model becomes easier overall. Existing opaque contractions need
an expression presentation; symmetry discovery and nonpolynomial functions
are not supplied. There is no analytic action integral, boundary-condition
theorem, quantum equivalence or higher-order field-redefinition result.
