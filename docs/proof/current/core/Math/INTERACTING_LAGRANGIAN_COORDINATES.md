# All-Order Interacting Coefficient Coordinates

Every admitted local polynomial Lagrangian has an exact all-order coordinate
description of its invariant coefficients modulo full generated EOM and IBP.
Extraction and reconstruction are inverse. No field-number or derivative-order
cutoff and no caller-supplied relation-completeness premise enter the theorem.

## Input And Meaning Of Classification

Take `L : Math.LocalPolynomial.Expr F B I`, a supplied representation `rho`
of a group H on the actual exterior/polynomial jet algebra A, and proof that
the full generated relation module is stable under rho. The trivial-action
entry supplies this proof automatically. The syntax admits any finite
polynomial interaction and finite ordinary derivative words, including
degenerate densities; no kinetic nondegeneracy is assumed.

The result classifies **all complex linear coefficient functionals** by
necessary and sufficient linear conditions on their monomial values. The
solution space can be infinite. It does not supply a terminating elimination
algorithm, finite basis or closed dimension formula for every Lagrangian.
The chosen odd-jet ordering is a noncomputable coordinate convention.
Neither it nor a chosen vector-space basis is a physical assumption.

## Actual Basis And Generated Equations

The source basis is indexed by

$$
\mathcal M=\mathrm{Finset}(J_F)\times(J_B\to_0\mathbb N),
\qquad J_F=F\times(I\to_0\mathbb N),\quad
J_B=B\times(I\to_0\mathbb N).
$$

It is the tensor product of the actual exterior-algebra and polynomial
monomial bases. Arbitrary finite odd sets, even exponents and jet orders
occur. A coordinate family is a function c:M→ℂ, with no finite-support
condition. Evaluation on any source polynomial is a finite sum, because
that polynomial's basis representation has finite support.

For basis elements b_i and every computed Euler component E_s(L), rows are

$$
b_i D_w E_s(L)b_j,\qquad D_a b_j.
$$

Both multipliers, every finite derivative word w and every field label are
included. The first rows span the full two-sided differential EOM closure;
the second span the actual linear divergence range. The proof expands both
multipliers in the basis and uses the independently proved differential
normal form. IBP is not ideal-closed.

Reconstruction f_c is admissible exactly when it kills all these rows and
obeys f_c(rho(g)b_i)=c_i for every actual group element and basis index.
The all-order equivalence, both inverse laws, reconstruction, prescribed-value
iff and prohibition/allowance iff are proved. Full-group invariance is not
replaced by Lie-generator tests.

## Selected Sources

For an invariant subspace V, selected rows are all finite combinations of
the full rows whose actual sum lies in V. Their span is proved equal to the
full relation preimage. This retains cancellations involving arbitrarily
high rows; it does not truncate equations at V's degree.

A supplied basis of V gives selected coordinates. An internally chosen basis
is also available, noncomputably. The equivalence classifies all selected
coefficients directly, without assuming they extend to global invariants.
Nonlinear EOM may mix grades; no independent graded quotient is asserted.

## Closed Interacting Example And Counterexamples

For the polynomial potential lambda*X^(n+1)/(n+1), in one variable with no
spacetime directions, differentiation gives lambda*X^n. Its **entire**
coefficient sequence is admitted exactly when

$$
\forall k\in\mathbb N,\quad \lambda c_{n+k}=0.
$$

For nonzero lambda this gives inverse free coordinates `Fin n → ℂ`; for
lambda=0 it gives all sequences `ℕ → ℂ`. A prescribed value c on X^m exists
exactly when lambda=0, m<n, or c=0. This includes nonlinear n≥2 and the
degenerate n=0 equation. It is an artificial algebraic model, not a
four-dimensional interacting operator count.

There is no input-independent degree cutoff, and even the fixed zero
interaction has nonzero coefficients invisible below any chosen order.
Cancelling opposite potential terms gives zero EOM, whereas imposing both
separate Euler families removes genuine coefficients. These refute those
shortcuts; they do not prove undecidability of a general decision problem.

## Entry Points And Evidence

- [All-order input coordinates](../../../../../Math/RepresentationTheory/Lagrangian/AllOrderDerivativeCoordinates.lean).
- [Actual monomial basis](../../../../../Math/Algebra/Jets/MixedJetMonomialBasis.lean).
- [Full generated row span](../../../../../Math/Algebra/Jets/DifferentialBasisRows.lean).
- [Mixed Lagrangian factory](../../../../../Math/RepresentationTheory/Lagrangian/InteractingLagrangianCoordinates.lean)
  and [bosonic factory](../../../../../Math/RepresentationTheory/Lagrangian/BosonicAllOrderCoordinates.lean).
- [Exact selection](../../../../../Math/RepresentationTheory/Lagrangian/AllOrderSelectedCoordinates.lean).
- [Polynomial potential classification](../../../../../Math/RepresentationTheory/Lagrangian/PolynomialPotentialClassification.lean)
  and [artificial controls](../../../../../Math/RepresentationTheory/Lagrangian/InteractingLagrangianControls.lean).
- [Literature consumers](../../../../../Physics/FieldTheory/Jets/Lagrangian/InteractingLagrangianLiterature.lean),
  [source-specific results](../../../../topics/interacting-lagrangian-classification/literature-validation.md)
  and [verification](../../../../topics/interacting-lagrangian-classification/verification.md).

Ordinary derivatives, supplied symmetry and complex independent field labels
retain their existing meaning. The theorem does not infer physical reality,
local gauge symmetry, analytic dynamics or higher-order field-redefinition
equivalence from an arbitrary density. The generated source and represented
inputs remain the existing published interfaces.
