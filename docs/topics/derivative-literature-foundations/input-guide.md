# Generated Inputs From The Proved Foundations

These are additional constructors of the existing `Math.DerivativeInterface.Input`.
Choose between graded IBP, full EOM and these represented model entries in the
[common input guide](../derivative-interface-adapters/input-guide.md).
The shared operations and published nonderivative inputs keep their existing
types and proof obligations. Finite coordinate certificates remain optional.

## Higgs Density

Import `Physics.FieldTheory.Jets.HiggsStandardInput` and use
`GUT.HiggsStandardInput.input a b`. The supplied a,b determine

\[
L=(\partial H)^\dagger\partial H-a\rho-\tfrac b2\rho^2,
\qquad \rho=H^\dagger H.
\]

The complete component equations and their derivative descendants/products
are generated. Weak/hypercharge and Lorentz actions and their full relation
stability are packaged once. The caller uses the existing `P.Source`,
`P.Coefficient`, `P.projection`, `P.coefficientEquiv` and evaluation operations.
`GUT.HiggsStandardInput.coefficientEquiv` compares with the independently
specified direct equations, with both inverse laws and unchanged evaluation.

This entry uses ordinary derivatives, a complexified Higgs/dual component
algebra, global internal symmetry and signature (+---). Real a,b may be cast
into the complex parameters. It does not turn arbitrary additional terms
into automatically invariant interactions. A new term may use the generic
expression helper and retain its own stability proof until a supported
represented entry is proved.

`Math.HiggsLagrangianInput.input a b` is the corresponding generated component
input with trivial action. `GUT.HiggsLagrangianInput.input a b` retains actual
Lorentz symmetry alone. Those entries do not silently imply the full
SM internal action; choose the represented entry for that requirement.

Every coefficient of the represented entry satisfies the exact relation
between rho times kinetic, rho times box rho, rho squared and rho cubed.
The input does not independently parametrize arbitrary values on those
representatives or prove a nonzero invariant coefficient exists.

## Paired Weyl Kinetic Input

Import `Physics.FieldTheory.Jets.PairedWeylGeneratedInput` and use
`GUT.PairedWeylInput.generated`. The helper generates both left and conjugate
Weyl equations in the full mixed jet algebra with off-shell Higgs spectators.
Actual SL(2,C) symmetry and stability of all products/descendants and IBP
are packaged. `GUT.PairedWeylInput.coefficientEquiv` compares with `direct`,
with both inverse laws and unchanged evaluation. The ordinary common input
operations apply to this full source.

This fixed kinetic entry does not infer symmetry for new interactions.
It does not impose Higgs EOM, weak/hypercharge action or a four-component
current dictionary. The [mixed record](mixed-input.md) separates those gates.

## Finite Coordinates And Scalar Controls

`Math.FiniteDerivativeCertificate.Presentation P` asks for an actual finite
carrier basis (U in `P : Input H U`, before quotienting) and a relation
family with a proved span equality to `P.relations`. For an infinite jet
carrier, use a finite stable selection with its full relation preimage. Its
`equivalence` converts coefficients to relation-annihilating, full-group
invariant coordinate vectors and back. It does not compute these proofs
from an arbitrary matrix. The complete quadratic example is in
`Math.FiniteDerivativeScalarControl`.

`GUT.ScalarConstantCoefficients.functional n` is a global free Lorentz
coefficient taking phi^n to 1. `cubic_value_iff` gives the exact admitted
cubic values in the interacting scalar input. The
[finite record](finite-certificates.md) states the complete derivative-degree
zero image result and remaining positive-degree basis obligations.
Existing published input routes remain valid.

## Checked Literature Examples

The [renewed six-case comparison](literature-recheck.md) uses these entries
in reproducible [Lean consumers](../../../Physics/FieldTheory/Jets/DerivativeLiteratureRecheck.lean).
For the real mass/quartic convention of Grzadkowski et al., use Higgs
parameters a=-m2 and b=lambda. `C3.derivative_only_iff` checks exactly when
discarding the potential contribution preserves a given coefficient value.
For the paired Weyl entry, `C5.conserved_products` and
`C5.symmetric_current_zero` use both generated EOM and actual IBP.
These examples do not supply an arbitrary basis solver or the unproved
physical-current translation.

The [nonderivative input recheck](nonderivative-recheck.md) covers the other
use of the integrated entry: import an original exterior/symmetric
coefficient with `DerivativeInterface.fromNonDerivative` and use the same
operations at d=0. Concrete Bose/Fermi/mixed and finite-local examples have
inverse evaluation checks. Full EOM model inputs can also take nonderivative
targets, with the additional equation relations retained. The scalar cubic
test and actual Higgs potential selection show this distinction explicitly.

## Presentation And Reality Checks

`Math.InputPresentation.coefficients` transports coefficients along an
equivariant source equivalence with proved equality of the mapped full
relation module. `reexpress` constructs both transported action and relations
from a linear source equivalence; evaluation and inverse laws are proved.
Its seed-scaling and row-recombination lemmas preserve the complete EOM/IBP
module. See the [concrete additional checks](extended-checks.md).

`GUT.ScalarRealityChecks.adjoint` applies to the actual scalar input at a
real coupling. Its real fixed-image equivalence covers all free d=0 scalar
classes. Reality is an additional condition; arbitrary complex couplings
or newly supplied mixed interactions receive no automatic Hermitian
interpretation. The paired Weyl and conjugate-coordinate controls have
their separate boundaries in the same report.
