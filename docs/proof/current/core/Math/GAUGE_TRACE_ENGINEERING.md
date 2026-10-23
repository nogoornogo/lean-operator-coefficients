# Formal Unit Gauge Covariance, Trace IBP And Engineering Sources

For an associative complex algebra with the retained ordinary linear Leibniz
derivatives and their commutation, `Math.FormalConnection.gauge` transforms a
connection by an arbitrary internal unit. The inverse derivative formula,
adjoint covariant derivative transformation, curvature and signed EOM
conjugation, identity and composition are proved. The unit is not assumed
derivative-constant. A nonconstant polynomial matrix unit produces a nonzero
flat transformed connection.

For finite matrices over a commutative complex differential algebra,
`Math.MatrixTraceIBP` constructs entrywise ordinary derivatives, proves zero
trace for commutators, trace/derivative compatibility and covariant trace IBP.
The ordinary divergence on the right gives the identity in the actual linear
EOM/IBP quotient for every polynomial seed set. The construction uses the
parent's inverse quotient/coefficient comparison; it does not ideal-close IBP.

`Math.JetEngineering` assigns a jet variable weight `1 + jet order`. Products
add degrees and ordinary derivatives add one. Positive weights and bounded jet
orders prove finite monomial sets and finite-dimensional fixed-degree sources
for finite species/directions. Images in the actual EOM and full EOM/IBP
quotients are finite-dimensional. No global interacting quotient grading or
normal-form theorem is inferred from this image construction.

`Math.ScalarEngineeringTwo` proves complete monomial reconstruction at degree
two: a single scalar square and all first jets span the entire source. The
physical consumer proves which classes vanish and which survive in the full
unbounded relation quotient.

Sources:

- [Local unit identities](../../../../../Math/Algebra/Constructions/FormalGaugeTransformation.lean).
- [Trace and actual quotient IBP](../../../../../Math/Algebra/Jets/MatrixTraceIBP.lean).
- [Nonconstant polynomial unit](../../../../../Math/Algebra/Constructions/FormalGaugeExample.lean).
- [Engineering weights and finite images](../../../../../Math/Algebra/Jets/JetEngineeringDegree.lean).
- [Complete degree-two source](../../../../../Math/Algebra/Constructions/ScalarEngineeringTwo.lean).
- [Strict transitive audit](../../../../../Math/Algebra/Constructions/Audit/AuditGaugeEngineering.lean).

The [topic result](../../../../topics/gauge-covariance-engineering/results.md)
and [verification](../../../../topics/gauge-covariance-engineering/verification.md)
own the checked scope and commands. The gauge formulas are internal algebraic
identities; no action on an independently presented connection ring, local
gauge orbit quotient, variational principle or analytic field equivalence is
assumed or asserted.
