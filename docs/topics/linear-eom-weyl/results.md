# Linear Equations, Weyl Sources And Formal IBP

## Common Linear Equation Construction

For a specified complex linear seed map `e : E → J`, where `J` is the actual
component-labelled jet module, the equation relations are constructed as

\[
N_e=\mathrm{span}_{\mathbb C}
  \{p(\partial)e(x):p\in\mathbb C[\partial],\ x\in E\}.
\]

Polynomial multiplication acts on the existing multi-index presentation.
The relations contain every seed and every derivative descendant. Their
shift stability and the commuting quotient shifts are proved. For arbitrary
systems, an explicit equivariant seed map is the covariance hypothesis;
the relation module's stability then follows. It is not supplied independently.
The existing scalar equation is recovered by `e(v)=q·v`: `scalar_relations`
proves equality with its original relation module, and `scalarEquiv` and
`scalarEquiv_shift` identify the quotients and derivatives. Old proofs remain
unchanged. A zero seed has zero relation module.

For odd and even systems, the actual on-shell algebra is

\[
\Lambda(J_F/N_{e_F})\otimes_{\mathbb C}
  \mathrm{Sym}(J_B/N_{e_B}).
\]

The projection from the existing mixed exterior/polynomial jet algebra is
constructed and proved onto. Even derivations descend, satisfy the Leibniz
rule and commute. The actual group action and derivative covariance are
proved, including compatibility with projection. The kernel of this actual
projection is the EOM kernel. No candidate relation matrix, source span or
coefficient completeness premise is substituted for it. A separate two-sided
ideal presentation for the mixed noncommutative algebra is not asserted.

## Fixed Grades, IBP And Coefficients

Fixed `(n,m,d)` spaces are **images** of the existing off-shell mixed grades.
They are finite-dimensional for finite component and direction sets. There
is no global direct-sum claim for an arbitrary inhomogeneous equation system.
The derivative maps those image grades to the next derivative grade.

The on-shell IBP submodule is the actual divergence range. It equals the image
of the off-shell divergence range under grade projection. Thus, for target
grade `d+1`, there is a constructed inverse linear equivalence

\[
U_{\mathrm{off}}/(\ker\pi+R_{\mathrm{IBP,off}})
\simeq U_{\mathrm{shell}}/R_{\mathrm{IBP,shell}}.
\]

Both actions are constructed and this equivalence is equivariant. Representative
formulas, inverse coefficient transport and invariant coefficient descent are
checked. IBP is a linear divergence range, without ideal closure. For a
constructed product action `L × H` on these sources, the local-coinvariant
and finite-residual evaluation interface retains degree cutoffs
`orbitSize(s)-1` and `|H|-1` at every constant spurion value. Intrinsic local
component actions are allowed. Generic seed covariance remains explicit;
the physical Weyl case below discharges it. Only the finite residual group
is averaged. This adds no general algebraic-group saturation theorem.

## Actual Left-Chiral Weyl System

The component representation is the existing SL(2,ℂ) fundamental left action;
directions carry the existing dual four-vector action in signature `(+---)`.
The seed uses the dual Pauli contraction followed by a first-jet frame.
`contract_covariant`, `frame_covariant` and `seed_covariant` prove the actual
intertwining. Equation parameters carry the **dual right-spin** action.
This is derived from the Pauli action, not assumed from a literature formula.

In the repository's source-vector convention, the two seeds are

\[
\begin{aligned}
r_0&=(\partial_0+\partial_3)\psi_0+
       (\partial_1+i\partial_2)\psi_1,\\
r_1&=(\partial_1-i\partial_2)\psi_0+
       (\partial_0-\partial_3)\psi_1.
\end{aligned}
\]

Their explicit formulas and off-shell nonzero values are proved. Both vanish
in the quotient, along with every polynomial derivative multiple. The wave
relations on both components are consequences of these first-order equations;
the wave equation alone does not define this Weyl model. The source/dual
convention is essential: equality with a paper's classical field column and
raised/lowered index notation is not claimed.

At the formal null point `(1,0,0,1)`, polarization `(0,1)` annihilates all
relations. The induced probe detects `∂₀ᵏψ₁` for every natural `k`. These jets
survive in the quotient generator module, the exterior algebra and the actual
mixed on-shell algebra with free scalar spectators. The latter is checked
using a linear tensor probe. Higher jets are therefore not truncated.

`sourceEquiv` and `coefficientEquiv` instantiate the common actual finite
EOM/IBP comparison and coefficient descent with this proved Weyl action.
Nonzero jet controls are before IBP; they do not assert a nonzero one-field
Lorentz-invariant integrated operator or classify a 4D invariant basis.

## Source Map And Remaining Boundaries

- [Linear jet systems](../../../Math/Algebra/LinearJetEquation.lean).
- [Actual quotient algebra](../../../Math/Algebra/LinearJetAlgebra.lean) and
  [actions](../../../Math/RepresentationTheory/LinearJetAction.lean).
- [EOM/IBP comparison](../../../Math/RepresentationTheory/LinearJetIBP.lean) and
  [finite-group spurions](../../../Math/RepresentationTheory/LinearJetSpurion.lean).
- [Actual Weyl seed](../../../Physics/FieldTheory/Jets/WeylLinearEquation.lean),
  [controls](../../../Physics/FieldTheory/Jets/WeylEquationControls.lean) and
  [physical EOM/IBP consumer](../../../Physics/FieldTheory/Jets/WeylEquationIBP.lean).

The endpoint is one free massless chiral system. Conjugate/right or massive
and interacting equations, gauge curvature/Bianchi identities, variational or
analytic actions, amplitude/momentum comparisons, full EFT counts and physical
matching/rates remain separate. See the [source register](references.md) for
inspection and attribution limits and [verification](verification.md) for
the strict audits and actual build evidence.
