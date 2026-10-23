# Optional Local Polynomial EOM Generator

This is an optional construction of the existing derivative coefficient input,
not a replacement for direct equations or the published nonderivative API.
See the [input guide](../../../../../topics/local-lagrangian-helper/input-guide.md),
[results](../../../../../topics/local-lagrangian-helper/results.md) and
[verification](../../../../../topics/local-lagrangian-helper/verification.md).

| Module | Interface and proved role |
| --- | --- |
| `Math.Algebra.Constructions.LocalPolynomial` | Finite syntax, actual mixed-jet evaluation, word derivatives, parity and first-variation comparison |
| `Math.Algebra.Jets.MixedJetParity` | Actual mixed involution and generator sliding |
| `Math.Algebra.Variational.VariationalIBP` | Noncommutative word adjoints and explicit finite-support IBP currents |
| `Math.Algebra.Variational.LocalEuler` | Automatic variation terms, finite-support Euler coefficients and universal pre-quotient identity |
| `Math.Algebra.Jets.TwoSidedDifferentialRelations` | Least two-sided differential relation closure and exact commutative-ideal specialization |
| `Math.RepresentationTheory.Lagrangian.LagrangianInput` | Generated mixed EOM/IBP factories using existing common operations |
| `Math.RepresentationTheory.Lagrangian.BosonicLagrangianInput` | Existing scalar equations factory, actual evolutionary derivative/substitution comparison |
| `Math.Algebra.Variational.LagrangianControls` | Scalar, derivative, higher-order and actual Grassmann convention checks |
| `Physics.FieldTheory.Jets.Lagrangian.LagrangianHelper` | Actual Lorentz scalar with generated sixth-power interaction, packaged symmetry and coupling-only input |

The admitted expressions have fixed complex coefficients, arbitrary component
types and finite derivative words; no degree/order cutoff or kinetic
nondegeneracy is assumed. The variation theorem requires parity-preserving
components. The generic represented factory requires combined-relation
stability; the trivial factory does not request a residual symmetry.

Generated equations include all products and descendants. Their mixed closure
is two-sided, while divergences remain a linear range. The commutative bridge
identifies the old relation source exactly, without a new quotient grading.
The actual first-variation identity holds before either quotient. Bosonic
four-direction substitution comparison retains all higher epsilon terms;
only the first coefficient is identified.

The two strict audits cover every declaration in the new Math and consumer
namespaces, including generated helpers, and check transitive axioms and
source-layer imports. Only the three existing standard axioms are permitted.
No analytic, literature, quantum or arbitrary-symmetry premise is imported.
