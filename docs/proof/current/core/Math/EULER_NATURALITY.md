# Euler Naturality Of Local Polynomial Densities

The computed Euler family of a finite local polynomial depends only on its
value in the actual mixed ordinary-jet algebra. Compatible global linear field
and direction actions carry this family by the variational chain rule.
Invariant densities therefore supply full EOM/IBP relation stability.

## Statements And Inputs

The algebra is the tensor product of the exterior algebra on odd jets and the
polynomial algebra on even jets. A jet label is a field component and a
commuting derivative multiindex. `jetPartial` uses actual left Clifford
contraction for odd jets and polynomial differentiation for even jets.
The finite gradient agrees componentwise with these derivatives. The Euler
family sums the multiindex formal adjoint applied to the corresponding partial.

`Expr.euler_eq_of_eval_eq` proves that equal evaluated densities have equal
Euler families, including Grassmann reordering and permutations of ordinary
derivative words. No fixed degree or order cutoff is used.

`Prolongation.euler_natural` takes a parity-compatible linear jet substitution
with algebra map rho, base-field map R, and constant direction matrix C.
The algebra map carries D_i(a) to the sum of C_ij D_j(rho(a)). The jet map has
the same prolongation law and restricts to R on zero-order fields. These are
transformation-data premises, independent of the density L. If q evaluates to
rho(L), the result is

```text
E_t(q) = sum_s R_ts rho(E_s(L)),    R_ts = (R e_s)_t.
```

Naturality itself does not require invertibility. For invariant L and
invertible R, `invariant_euler_span` solves this identity using R inverse.
Every transformed Euler component lies in the original Euler-family span.
Existing covariance then proves stability of the entire two-sided differential
EOM closure and the linear IBP divergence range.

## Standard Input

`StandardDensityAction.model` constructs the action certificate from supplied
group representations on odd fields, even fields and derivative directions.
Their group actions provide invertibility. The only Lagrangian-dependent
symmetry premise is invariance of the evaluated density. No Euler-covariance
or first-variation identity is requested from the caller. The result is the
existing `LagrangianModel.Mixed`, with unchanged input, all-order coordinates,
coefficient decoder and selected-source operations. Empty odd labels include
purely bosonic densities.

Only the direction index needs a `Fintype` for finite covariance sums. Field
labels may be arbitrary; each expression and every generator image has finite
support. Any finite polynomial degree and ordinary-jet order are permitted.

## Proof Structure And Scope

1. Actual graded partial derivatives satisfy the twisted Leibniz rule.
2. Syntax linearization gives their finite coordinate family. Commuting total
   derivatives make adjoints independent of the chosen derivative word.
3. The graded linear chain rule transports this family. Formal adjoints cancel
   the prolonged direction transformation, leaving the base-field map.
4. Invertibility and density invariance supply Euler-span stability and the
   established full-relation input.

Density invariance is equality in the specified jet algebra. Manifold volume
and Jacobian transformations, nonlinear field changes, local gauge connections
and analytic action integrals are not constructed. The constructor uses proofs;
it does not discover symmetries or solve every all-order coefficient system.

## Evidence

- [Semantic descent](../../../../../Math/Algebra/Variational/SemanticEuler.lean).
- [Graded chain rule](../../../../../Math/Algebra/Jets/LinearJetSubstitution.lean).
- [Euler naturality](../../../../../Math/Algebra/Variational/EulerNaturality.lean).
- [Density symmetry](../../../../../Math/RepresentationTheory/Lagrangian/DensitySymmetry.lean).
- [Standard constructor](../../../../../Math/RepresentationTheory/Lagrangian/StandardDensityAction.lean).
- [Input guide](../../../../topics/euler-naturality/input-guide.md).
- [Comparisons](../../../../topics/euler-naturality/literature-validation.md).
- [Verification](../../../../topics/euler-naturality/verification.md).
