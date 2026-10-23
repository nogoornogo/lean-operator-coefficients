# Optional Lagrangian-To-EOM Helper

Use this helper when adding or changing polynomial interactions would otherwise
require deriving new EOM by hand. Direct EOM input remains available and may be
simpler for an already registered model. This is a Lean expression API; it does
not parse textbook notation or automatically discover index contractions.

For a reusable density/action package, use the
[model-facing guide](../lagrangian-model-connections/input-guide.md).
Registered scalar, Higgs and scalar/Weyl Yukawa entries expose the same input,
all-order coordinates, evaluation and selected-subspace operations.

## Enter A Density Once

```lean
import Math.RepresentationTheory.BosonicLagrangianInput

open Math.LocalPolynomial
noncomputable section

def phi : Expr Empty Unit (Fin 4) := Expr.boson ()
def L (g : ℂ) : Expr Empty Unit (Fin 4) :=
  (1/2 : ℂ) • (Expr.derivative 0 phi)^2 - (g/6) • phi^6

def model (g : ℂ) := (L g).scalarTrivialInput
```

`(L g).scalarEuler ()` is generated from L. No EOM expression or proof of a
first-variation identity is a factory argument. Add a derivative interaction
by changing L, for example `phi^2 * (Expr.derivative 0 phi)^2`; rebuild the input
with the same call. `L.euler` returns the mixed-algebra finite-support Euler
family; `L.boundary eta` generates explicit finite-support currents.

Constants use `Expr.constant c`, field jets use `Expr.jet label word`, and
`Expr.sum` combines a list of expressions, for example a finite contraction.
Products, scalar multiplication, subtraction and natural powers use ordinary
Lean notation. There is no fixed field-degree or derivative-order cutoff.
The expression presentation itself is not a ring instance: algebraic identities
hold after `eval`/`scalarEval`, rather than as equality of syntax trees.

The component types reuse existing field labels. Factor order matters for odd
fields. A contraction can be defined once as an expression-building function
and then reused. An existing opaque tensor functional/algebra element is not
automatically converted into this syntax; its component expression must be
provided. Conjugate fields and reality conditions retain their supplied model
dictionary. Every field label in the generated seed family is varied;
nondynamical background equations are not automatically excluded. Fixed
couplings and inverse scales can be supplied as complex constants;
field-dependent functions must be expressed using the admitted polynomial
operations. Exponentials, logarithms and inverse functions of fields are not
silently truncated.

## Choose The Existing Output Route

| Need | Call | Additional caller input |
| --- | --- | --- |
| Bosonic jets on the existing polynomial source | `L.scalarTrivialInput` | None when no residual symmetry is requested |
| Bosonic jets with residual symmetry | `L.scalarInput rho stable` | Existing source action and generated full-relation stability |
| Mixed Bose/Fermi jets | `L.trivialInput` | None when no residual symmetry is requested |
| Mixed jets with residual symmetry | `L.input rho stable` | Existing source action and generated full-relation stability |
| Actual Lorentz scalar kinetic term with sixth-power potential | `GUT.ScalarLagrangianHelper.input g` | Coupling only; import `Physics.FieldTheory.Jets.LagrangianHelper` |

The scalar route returns the existing commutative `DerivativeInterface.equations`
input with generated seeds. The mixed route uses a proved two-sided differential
closure and the same `DerivativeInterface.Input` operations. Both retain the
full source; nonlinear EOM can mix degrees. Divergences are a linear range,
not an ideal closure.

After construction, use `P.Source`, `P.Coefficient`, `P.projection`,
`P.coefficientEquiv`, `P.extraction`, `P.reconstruction`, `P.nonzero_iff` and
`P.forbidden_iff` exactly as in the [existing input guide](../derivative-interface-adapters/input-guide.md).
The helper constructs the relation input; it does not enumerate coefficients,
prove that every input has a nonzero coefficient, or solve the resulting EOM.

## Mixed Example And Signs

```lean
open Math.LocalPolynomial

def psi (b : Bool) : Expr Bool Unit Unit := Expr.fermion b
def h : Expr Bool Unit Unit := Expr.boson ()
def interaction (g : ℂ) := g • (h * psi false * psi true)
def mixedModel (g : ℂ) := (interaction g).trivialInput
```

The generated left-variation coefficients are `g*h*psi true` for the first
odd field and `-g*h*psi false` for the second. The even coefficient is
`g*psi false*psi true`. The [compiled controls](../../../Math/Algebra/LagrangianControls.lean)
compare these with actual left Grassmann contractions and check reordering
and odd square cancellation. This is an algebraic mixed example, not a claim
that these component labels already form a Lorentz spinor contraction.

`Expr.first_variation` applies to arbitrary parity-preserving polynomial
variations: odd fields receive odd components, even fields receive even
components. This is a premise of the mathematical variation theorem, not an
argument required to compile L or construct its input. In four-dimensional
bosonic jets, the result agrees with the existing actual evolutionary
derivation and degree-one substitution coefficient.

## What Work Is Saved

The compiler generates EOM coefficients, derivative descendants through the
relation construction, and first-variation currents. In the compiled examples,
changing an interaction changes the expression and the factory call's input;
it does not require entering a new EOM formula. The actual Lorentz scalar
consumer packages its symmetry proof once and exposes only g.

Generic symmetry preservation, representation choices and contraction
correctness remain model obligations. A new term need not preserve a requested
symmetry. No generic symmetry proof is inferred from the word “Lagrangian”.
The examples demonstrate this specific reduction of caller work; they are not
a measured user study or a universal performance claim. Repeated derivative
expansion may produce large syntax. Existing registered inputs remain useful
when their packaged data already suffice.

## All-Order Coefficient Coordinates

Import `Math.RepresentationTheory.BosonicAllOrderCoordinates` for
`L.scalarTrivialAllOrderEquivalence`, or
`Math.RepresentationTheory.InteractingLagrangianCoordinates` for the mixed
`L.trivialAllOrderEquivalence`. For a requested symmetry use
`L.scalarAllOrderEquivalence rho stable` or `L.allOrderEquivalence rho stable`.
Registered Higgs entries already package their action and stability proofs.

These are inverse maps between the existing generated input's coefficients
and families of all monomial values obeying the complete generated EOM,
IBP and group-action rows. Each density is evaluated by a finite sum;
the coordinate family and row system extend over all degrees. No new basis,
rank or relation-span proof is requested for the full source.

For an invariant selected subspace V, the presentation's
`canonicalSelectedEquivalence V hV` supplies chosen coordinates internally;
`selectedEquivalence V hV basis` uses a preferred basis. Both retain the
full relation preimage. Selected coefficients need not extend to global
invariant coefficients, so use the selected equivalence for that question.

The general result gives necessary and sufficient equations, rather than
solving every infinite system automatically. A complete closed example
classifies the potential lambda*X^(n+1)/(n+1) at every order, including zero
coupling. See the [all-order dossier](../../proof/current/core/Math/INTERACTING_LAGRANGIAN_COORDINATES.md)
and [literature/artificial validation](../interacting-lagrangian-classification/literature-validation.md).
Form the total density before generating Euler equations: individual terms
can cancel, and the union of their separate equation ideals need not equal
the equations of their sum. Adding interactions also changes which earlier
free-input completeness theorems apply.


For constant linear global field/direction actions, the
[invariant-density constructor](../euler-naturality/input-guide.md) now derives
Euler covariance and full EOM/IBP stability from evaluated density invariance.
It returns the existing model input and accepts any finite polynomial jet order.
