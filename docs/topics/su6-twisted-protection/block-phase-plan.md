# Standard-block inner action with external fourth-root phases

Test one explicit candidate on the existing topic branch. No general
classification is requested. Use the standard basis of `15 + bar6 + bar6`,
the inner generator `g = diag(1,1,1,-1,-1,1)`, and external generator
`E = diag(i on 15, i on first bar6, -i on second bar6)`.
The physical generator is `U = rho(g) E`; the residual group is C4.
Use the adjoint vacuum `diag(1,1,1,1,1,-5)` with neutral external scalar
action. Choose the six Dirac pairs `(15[a,6], second bar6[a])`, a=1,...,5,
and `(first bar6[6], second bar6[6])`, with unit symmetric coefficients.
This is the standard full-gauge mass benchmark's pairing pattern, in an
explicit component normalization; its coupling to a UV scalar sector is not
supplied. The light dictionary is Q/u^c/e^c from 15 and d^c/L from first bar6.

Endpoint: exact, reproducible finite checks of order, inner covariance,
vacuum fixedness, standard gauge/mass invariance, actual mass radical, and
the action on the existing one-generation Lorentz/Grassmann qque contraction.
A surviving nonzero qque coefficient rejects this candidate as a symmetry
prohibition mechanism; it does not assert a generated interaction or decay.

Use Python standard-library integer arithmetic, rational elimination and
fourth-root exponent arithmetic. No sampled/numerical test, new dependency,
Lean theorem, quantum-exactness certificate, or other candidate is included.
Run the model audit and reused qque audit, local links and diff checks. Lean
sources are unchanged, so no new Lean build or axiom baseline is asserted.
