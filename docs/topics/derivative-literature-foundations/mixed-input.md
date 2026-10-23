# Mixed Weyl Equation Input And Current Boundary

## Supported Equations

[PairedWeylInput](../../../Physics/FieldTheory/Jets/PairedWeylInput.lean)
places the existing left and conjugate Weyl equations into the actual
exterior/polynomial jet algebra on Bool x Fin 2 odd and even labels. The
odd label distinguishes left and conjugate components; the even labels
are off-shell Higgs component spectators. The field action is the direct
sum of the existing left/right SL(2,C) representations. Directions carry
the existing dual Lorentz action in signature (+---).

Inclusions intertwine the full unbounded jet actions. Both equation maps
are covariant under their actual equation-parameter dual representations.
`TwoSidedCovariance` transports the complete two-sided differential equation
closure and the full linear divergence range. `direct` packages this
actual Lorentz input. Arbitrary products with spectator fields and all
ordinary derivative descendants are retained.

[PairedWeylKinetic](../../../Math/Algebra/PairedWeylKinetic.lean)
defines the ordered density chi_0 E_0(psi) + chi_1 E_1(psi), with the actual
Pauli component signs specified independently. Every odd Euler component
is computed: varying chi gives the left equations, while varying psi gives
the conjugate equations. Every even Euler component is zero. The equality
of full generated/component two-sided differential relations and IBP is
proved. This is an algebraic kinetic normalization; no analytic action or
reality/Hermiticity theorem is inferred.

[PairedWeylGeneratedInput](../../../Physics/FieldTheory/Jets/PairedWeylGeneratedInput.lean)
proves the actual Pauli row dictionary, their complete span over arbitrary
equation parameters, and equality of the generated/direct full relation
modules. `generated` packages actual Lorentz stability. `coefficientEquiv`
has both inverse laws, and `evaluation_agrees` preserves every polynomial
evaluation. The original C5 candidate can be evaluated through this new
equation input with unchanged generated/direct evaluation. `current_ibp`
retains all differentiated factors; no raw probe is used as a coefficient.

## C5 Current Gates

The structural route now supplies physical left/right equations, actual
Lorentz action and full mixed differential closure with spectators. These
were absent from the original trivial-action off-shell C5 test input. The
component route computes every helper Euler component and compares the
Pauli row signs with the existing Weyl sources. These checks do not prove
that the transcribed literature current is the required physical contraction.

The source locations remain Li v3 Eqs. (4.24)–(4.26) and Murphy v6 Table 5.
The existing Euclidean four-component adapter is not a Minkowski convention
bridge. That bridge must specify ordering, index raising, conjugation and
normalization and prove equality to the chosen current, followed by its
actual equivariance. Nonzero invariant quotient support and complete basis
span require separate proofs. Neither follows from admitting Weyl equations.

Higgs EOM, weak/hypercharge action on this mixed input, interacting Yukawa
terms and a complete dimension-eight basis are not imposed here. A's
separately proved Higgs input must not be silently combined with this one
as though that extra connection had been established. The C5 paper row
therefore remains partial.

The subsequent [C5 input/current result](../weyl-higgs-current-completeness/results.md)
adds a separate combined free Higgs/Weyl input with actual mixed internal
action, a Minkowski block-current dictionary and density equivariance.
The old off-shell spectator input above is preserved. The successor now proves a normalized invariant coefficient and complete
whole-grade scalar coordinate, with both inverse laws and dimension one,
within its fixed free one-flavor scope.

The subsequent [literature recheck](literature-recheck.md#c5--a-new-test-using-both-weyl-equations)
adds a concrete Pauli-current divergence identity and proves membership
in the generated two-sided EOM closure. Every admitted coefficient kills
its arbitrary products and the symmetric derivative current by IBP. This
is a new on-shell relation test, without the physical-current equivariance,
bidirectional-candidate nonzero or complete-basis assertions listed above.

The supported kinetic/input connection is proved. C terminates partially
at the stated physical-current dictionary and invariant-basis gates, after
the structural and component routes. No new interacting fermion theory is
recursively started. Earlier kernel normalization failures were repaired
with explicit seed-component equations and named span/closure lemmas;
they are development diagnostics, not the final semantic stop.
