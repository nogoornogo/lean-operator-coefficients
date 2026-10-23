# Invariant Density Input

Use this constructor for constant linear group actions on odd components,
even components and ordinary derivative directions. Write the total finite
local polynomial, then prove its evaluated invariance. The library derives
Euler covariance and full EOM/IBP stability.

```lean
import Math.RepresentationTheory.StandardDensityAction

open Math
noncomputable section
variable {F B I H : Type*} [Group H] [Fintype I]
variable (rF : Representation ℂ H (JetLinear.Field F))
  (rB : Representation ℂ H (JetLinear.Field B))
  (rI : Representation ℂ H (JetDirections.Direction I))
  (p : LocalPolynomial.Expr F B I)
  (hp : ∀ g, StandardDensityAction.action rF rB rI g p.eval = p.eval)

example : LagrangianModel.Mixed F B I H :=
  StandardDensityAction.model rF rB rI p hp
```

The model has existing `.input`, `.presentation`, `.equivalence`, `.evaluate`,
`.target_values_iff` and exact selected-source operations. Direct, generated
and nonderivative interfaces are preserved. Empty odd labels cover the
bosonic case. Polynomial degree and finite jet order have no fixed cutoff.

The representations are supplied once for the symmetry. Each interaction
needs evaluated density invariance; contractions, odd reordering and commuting
derivative words may be used. A transformation with a volume Jacobian needs
that additional geometric interpretation; this API uses the specified algebra
action.

For an existing custom action, `Prolongation` records its linear jet map,
parity and generator compatibility, base-field map and constant direction
covariance. `LagrangianModel.Mixed.ofInvariantDensity` accepts that certificate,
an invertible base-field map and density invariance. Neither constructor takes
Euler naturality as a premise. Other inputs can continue to use `ofEulerSpan`
or a full-relation certificate.

The full scalar/Weyl example is
[`EulerDensityConnection.automaticModel`](../../../Physics/FieldTheory/Jets/EulerDensityConnection.lean).
It uses actual Lorentz action and only `YukawaModel.density_invariant`.
`model_eq` proves equality with the previous independently certified model.
Its coefficient operations are therefore unchanged.

- [Theorem and assumptions](../../proof/current/core/Math/EULER_NATURALITY.md).
- [Literature and artificial validation](literature-validation.md).
