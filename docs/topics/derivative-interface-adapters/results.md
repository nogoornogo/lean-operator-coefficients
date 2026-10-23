# Result And Successful Stop

The [frozen connection contract](plan.md) is proved by additive adapters.
The published derivative-free sources and signatures are unchanged. A small
optional common-operation record is supplied for new derivative-side inputs;
existing callers gain no additional obligation.
See the [input recipe](input-guide.md) and [verification](verification.md).

## Added Relation Images

`Math.RelationInputExtension` accepts a proved coefficient equivalence
`C ≃ Hom_H(V,W)`, an explicit linear input map `q:U→V` and its evaluation
law. For an independently specified source relation T, it constructs
`q(T)` and proves

`{c in C | value(c)(T)=0} ≃ Hom_H(V/q(T),W)`.

Stability is derived when q intertwines the source action and T is stable.
No surjectivity of q, finite dimension or invariant complement is required.
Extraction, reconstruction, inverse laws, nonzero/forbidden criteria and
relation-free recovery are proved. The coefficient equivalence is an existing
proved input, not an assumed replacement for local completeness.

## Existing Finite Local Coordinates

`Math.FiniteLocalExtraRelations` uses the original contractions p, probes v,
normalization, local completeness, exchanges and signs. It computes

`q(u tensor w) = sum_i p_i(u) * [single i w]`

in the original independent statistics-relation quotient. For extra source
relations T it maps T into those coordinates, proves residual stability and
provides the extended residual-Hom equivalence. Reconstruction retains the
original contraction sum with the additional quotient projection. An actual
equivariant divergence map can be supplied directly: its range is stable and
the input condition is exactly vanishing on every divergence. No relation
matrix, basis discovery or new coefficient completeness premise is supplied.
Groups and flavor dimensions remain arbitrary. The new linear source adapter
uses additive-group complex modules; existing nonderivative hypotheses are
not altered.

## One Input For Zero And Positive Jet Grades

`Math.MixedOperatorInput.Coefficient` and `coefficientEquiv` accept every
natural-number derivative degree d. The source action always includes the
supplied direction representation. Relations are bottom at zero and the actual
covariant divergence range at d+1. Extraction, reconstruction, inverse laws
and a nonzero criterion use the same API at every degree.

`zeroSourceEquiv` extends the old zero-jet equivalence to arbitrary direction
mixing; its proof uses the zero-order intertwining identity on generators and
the actual exterior/symmetric source embedding. `nonDerivativeEquiv` imports
old coefficients inversely into the uniform zero-degree input, with forward
and inverse evaluation laws. `positiveInputEquiv` and `positive_map` prove
exact agreement with the earlier positive-degree input and map. No caller
selects a separate zero/positive descent theorem for a new input.

The lower-level `Math.JetInputAdapter.Input` remains definitionally the
existing `RelationQuotient.vanishing` input. Its earlier zero/positive bridges
are preserved, as are all published derivative-free sources.

`Math.JetAdapterControls` connects the complete actual mixed two-fermion,
one-boson, two-derivative source. Its input condition is precisely
`f(first)+f(second)=0`. The finite-local adapter with the explicit single
scalar contraction carries this same actual relation after tensor-coordinate
transport. Scalar contraction normalization and local completeness are proved
in this consumer, not postulated.

## Full Nonlinear Equations

The equation adapter uses the full polynomial differential ideal plus the
actual divergence range. Its condition is exactly annihilation of the whole
EOM ideal and of every `D_i(p)`. It needs stable relations for the supplied
residual action, without assuming a homogeneous or globally decomposed shell.

`GUT.ScalarInputAdapter` instantiates the existing interacting scalar algebra,
including its actual algebraic Lorentz direction action and proved covariance.
For every admitted coefficient it proves

`f(box phi) + lambda * f(phi^3) = 0`.

This explicitly retains relations between distinct field/derivative grades.
No EOM-constrained zero-grade recovery of the unconstrained original input is
claimed. The generic adapters also admit the previously proved mixed linear
EOM sources when their actual relation submodule and stability are supplied;
this result does not construct a new nonlinear fermionic differential ideal.

## Purpose-Specific Factories And Shared Operations

`Math.DerivativeInterface.graded` and `equations` return the same small
represented-input record. They keep different source requirements explicit:
actual mixed grade/IBP data versus full commutative EOM/IBP data. All previous
interfaces remain available. New callers use the same `P.Coefficient`,
`P.projection`, `P.coefficientEquiv`, extraction/reconstruction and nonzero/
forbidden criteria. Both factory inputs/maps are proved compatible with their
previous entry points, and old nonderivative coefficients enter through the
proved zero-jet equivalence. No new covariance premise is added to that route.

For an invariant subspace V, `P.select V hV` uses the preimage of the entire
relation submodule. `selected_kernel` and `selectionEquiv` identify its quotient
linearly with the actual image of V in the full quotient. Restriction of global
coefficients is a linear map with evaluation compatibility. Selected invariant
coefficients are not assumed to extend globally; selected images need not
form independent homogeneous components.

`Math.DerivativeInterfaceControls` compiles the shared operations on the actual
complete mixed source and retains its exact `first + second` relation.
`GUT.ScalarDerivativeInterface.scalar` packages the actual Lorentz scalar EOM
with coupling as the only caller input. Its selected invariant wave/cubic span
retains `f(box phi) + lambda*f(phi^3)=0` and has the proved full-quotient image
connection. This is explicit source selection, not a new nonlinear fermionic
EOM construction or an assertion that the scalar source decomposes by degree.
The [caller comparison](input-guide.md) records unchanged configuration/proof
requirements and shared operations; no empirical usability improvement is
claimed. The [purpose-specific contract](purpose-specific-plan.md) is complete.

## Scope

The necessary/sufficient criteria classify coefficient maps for the specified
source, symmetry and relations. Nonzero coefficients do not assert a generated
interaction, matching, rate or amplitude equivalence. Finite local contraction
completeness remains an explicit proved input. No universal local dictionary,
global on-shell grading, general Lagrangian input or analytic/quantum extension
is introduced. All contracted obligations close; the verified topic is
integrated into master.
See [merged-state verification](verification.md#master-integration).
