# Lorentz Jets And Free Massless Scalar EOM/IBP

## Actual Spin And Direction Actions

The group is the existing `Matrix.SpecialLinearGroup (Fin 2) ℂ`.
Pauli coordinates identify four complex coordinates with two-by-two matrices:

$$
\sigma(t,x,y,z)=
\begin{pmatrix}t+z&x-iy\\x+iy&t-z\end{pmatrix},
\qquad \det\sigma=t^2-x^2-y^2-z^2.
$$

`pauliEquiv` includes the inverse map. Transporting the actual action
`A ↦ M A M†` through it gives the four-component representation. Determinant
preservation proves invariance of the Minkowski quadratic form in signature
`(+,-,-,-)`. Real coordinates correspond to Hermitian matrices; the action
preserves this real subspace. These are proved algebraic statements.
No classification of the cover, its image/kernel or its topology is asserted.

The existing left Weyl action is `M`, and the right action is entrywise
conjugation. `left_right_matrix` proves that their outer product transforms
by `M A M†`. `weyl_basis` connects each existing action with the specified
free component basis used by the jet construction.

Derivative source vectors carry the **dual** four-vector representation.
If `L(g)` is the Pauli-coordinate vector action, the coefficient convention is

$$
c_{ji}(g)=L(g^{-1})_{ij}.
$$

`direction_single` proves this orientation. `weyl_derivative` proves the
first-derivative transformation with both its derivative and Weyl indices.
The [general direction package](../Math/DIRECTIONAL_JET_EOM_IBP.md) lifts
this action to all actual scalar/mixed jets, preserves the source grades and
provides inverse source and equivariant IBP coefficient transport.

## Scalar Metric Consumers

The symbol polynomial is

$$
q=p_0^2-p_1^2-p_2^2-p_3^2.
$$

`wave_invariant` proves its invariance under the actual dual action. Two
distinct equivariant evaluations give the linear higher-jet combination
`□φ` and the quadratic first-jet contraction

$$
K=(\partial_0\phi)^2-(\partial_1\phi)^2
  -(\partial_2\phi)^2-(\partial_3\phi)^2.
$$

`waveField_invariant` and `kinetic_invariant` certify these scalar consumers
in the actual polynomial algebra, without an invariant-ring completeness
claim or compact-group averaging.

## Massless Scalar Equation And Actual Quotient

The on-shell generator module quotients actual jets by every descendant
`[p q]`, with arbitrary symbol polynomial `p`. Its free scalar algebra is
equivalent to the original scalar polynomial algebra modulo the full EOM
ideal. `trace_zero`, `descendants_zero` and `waveField_zero` impose the trace
relation and its descendants. Stability, induced derivatives and covariance
are supplied by the general package with `wave_invariant` proved here.

For every field/derivative grade, `coefficientEquiv` gives inverse equivariant
descent through the actual on-shell divergence range.
`combinedRepresentationEquiv` identifies this construction with the off-shell
source modulo its EOM kernel plus its actual IBP relations, including the
SL(2,ℂ) actions. Symbol invariance and relation stability are proved for this fixed algebraic
scalar model. The equation defines the model; no variational derivation is claimed.

The four-dimensional control does not discard higher jets. Evaluation at the
null symbol point `(1,1,0,0)` annihilates `q`. It proves that **every** pure time
jet, of arbitrary order, remains nonzero in the on-shell generator module
and free scalar algebra, before taking IBP. Thus imposing traces is distinct
from truncating the higher-jet tower.

The actual current with components `φ ∂₀φ` and `-φ ∂ᵢφ` satisfies

$$
\sum_iD_i J_i=K+\phi\Box\phi.
$$

After EOM projection, this proves that `K` lies in the actual divergence range
and has zero IBP class. The separate one-direction
[complete regression](../Math/DIRECTIONAL_JET_EOM_IBP.md#complete-regression-and-boundaries)
proves the entire quadratic source quotient is zero. No full four-dimensional
operator table or invariant multiplicity classification is claimed.

## Inputs, Limits And Evidence

- [Pauli/direction action](../../../../../Physics/FieldTheory/Jets/Lorentz/LorentzDirections.lean),
  [scalar/Weyl IBP consumers](../../../../../Physics/FieldTheory/Jets/Lorentz/LorentzJetIBP.lean)
  and [massless scalar quotient](../../../../../Physics/FieldTheory/Jets/Scalar/Inputs/MasslessScalarEOM.lean).
- [Strict transitive audit](../../../../../Physics/FieldTheory/Jets/Lorentz/Audit/AuditLorentzScalarEOM.lean)
  and [verification](../../../../topics/derivative-ibp/verification.md).
- [Source reconciliation](../../../../topics/derivative-ibp/references.md#cde-implementation-source-reconciliation).

The narrow Pauli adapter is proved locally from the existing Weyl group and
Mathlib matrix/dual APIs. Physlib's corresponding Lorentz sources informed
the inspection, but its larger SM/Lorentz import closure and equality with
its coordinate map are not certified here. The Physlib even derivation
inputs remain the previously audited fragments. No dependency pin changes,
external physical premise, custom axiom or elaboration-limit increase is used.

The endpoint is ordinary commuting derivatives and free massless scalar EOM.
Weyl EOM, massive/interacting systems, gauge-covariant commutators, Bianchi
relations, disconnected Lorentz actions, analytic integration, S-matrix
equivalence and general EFT counting require separate statements.

## Separate Free Weyl Equation Extension

The [free left-Weyl extension](../../../../topics/linear-eom-weyl/results.md)
supplies a separate proved statement with the same actual SL(2,ℂ)/dual-direction
conventions. A dual Pauli contraction and first-jet frame prove the equation
seed intertwining; the equation parameters carry the dual right-spin action.
The explicit nonzero first-order sources and all descendants vanish on shell,
and imply the wave relations on both components. Null-polarization probes
retain higher time jets in the generator, exterior and actual mixed algebras
before IBP. The constructed mixed EOM/IBP comparison and coefficient descent
apply with scalar spectators. This is one free massless chiral system, without
a classical-field index comparison, conjugate/interacting equations, amplitudes
or full EFT enumeration. The extension owns its
[verification](../../../../topics/linear-eom-weyl/verification.md).

The subsequent [conjugate Weyl dossier](WEYL_CONJUGATE_IBP.md) adds the actual
right seed, inverse conjugate quotient maps and a paired exterior adjoint
compatible with EOM and the linear divergence quotient. It also proves the
complete four-dimensional single-field positive-derivative IBP source zero;
the earlier higher-jet probes concern the algebra before IBP.

The separate [free Abelian field-strength dossier](ABELIAN_FIELD_STRENGTH_IBP.md)
uses the same actual Pauli metric and direction convention for antisymmetry,
Maxwell and Bianchi source equations, wave consequences and finite EOM/IBP
transport. It retains its own verification and analytic/potential boundaries.
