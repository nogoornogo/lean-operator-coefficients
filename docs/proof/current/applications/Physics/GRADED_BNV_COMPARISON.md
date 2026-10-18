# Actual SM Comparison With Graded Completeness

## Result

[GradedBnvComparison](../../../../../Physics/StandardModel/Operators/GradedBnvComparison.lean)
instantiates [general quotient completeness](../../core/Math/GRADED_OPERATOR_COMPLETENESS.md)
with all ten signed SM fermions and the Higgs/gauge-dual scalar alphabet.
`perDegreeEquiv` identifies the independently defined nonzero-baryon support
at arbitrary mixed degrees with constructed residual-Hom products.
`sixComparison` and `sevenComparison` identify the general factors in degrees
`(4,0)` and `(4,1)` with the old explicit coordinates. `boundedSevenEquiv`
starts from the actual bounded-seven input and its proved degree decomposition.
Extraction/reconstruction diagrams commute with the
[existing equivalence](BNV_SEVEN_COMPLETENESS.md); both inverses and total
prohibition/nonzero iff are proved.

## Inputs And Conventions

The residual group is arbitrary. Flavor modules, including opposite species,
and both scalar modules are independent complex modules with their own actions.
No finite-dimensionality, self-duality or conjugate identification is assumed.
`fermion_eq` and `boson_eq` prove the constructed commuting local/residual actions
equal the existing field actions. The local group is SM gauge times Weyl.
The support selects nonzero sums in the existing integer `3B` convention.
Engineering weights are doubled dimensions, three per fermion and two per scalar.
The new theorem is degree-uniform; explicit old-coordinate comparison stops at seven.

## Proof And Verification

The original BNV submodule is identified with supported mixed functionals and
transported by proved representation equalities to the generic input. The new
generic restriction/quotient equivalence supplies the residual coordinates.
Comparison maps use the same actual input and proved inverses, not equal dimension
counts or an assumed dictionary. Existing positive/prohibiting controls transfer
through these equivalences.

The [strict audit](../../../../../Physics/StandardModel/Operators/Audit/AuditGradedBnvComparison.lean)
checks the interface and comparison diagrams transitively. Reproducible commands
and final evidence are in the [topic](../../../../topics/graded-operator-completeness/README.md).

## Boundaries And Citation Role

This is a connection theorem, not a new printed-basis certificate. Old local
dictionaries are proved consumers, not premises of the coefficient-space decomposition theorem.
There is no dimension-eight-to-eleven enumeration, finite all-degree cutoff,
inevitable-BNV, matching or rate claim. See [Physics assumptions](../../inputs/Physics/ASSUMPTIONS.md),
[the bounded-seven dossier](BNV_SEVEN_COMPLETENESS.md), and
[general assumptions](../../inputs/Math/ASSUMPTIONS.md).
