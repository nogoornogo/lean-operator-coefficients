# Lagrangian Model Packages

`Math.LagrangianModel.Bosonic` and `.Mixed` package a finite local polynomial
density, a specified group action and stability of its full Euler/IBP relation
module. Their inputs are the existing generated inputs; coefficient types,
quotients and nonderivative APIs are unchanged.

Their presentations reuse the
[all-order equivalence](../../core/Math/INTERACTING_LAGRANGIAN_COORDINATES.md).
Operations preserve evaluation, reconstruct coefficients and give necessary/
sufficient prescribed-value, prohibition and allowance criteria. Selections use
the full relation preimage; no invariant extension or finite rank is assumed.

`ofEulerSpan` requires a finite direction index, multiplicative action,
constant-matrix derivative covariance and transformed Euler components in the
span of the total Euler family. `LagrangianSymmetry` proves stability of the
whole two-sided differential closure and linear IBP. The bosonic factory uses
commutative/two-sided closure equality. A separate full stability proof can be
used directly without the finite-direction certificate route.

For constant linear field/direction representations,
`StandardDensityAction.model` derives the Euler certificate from evaluated
density invariance. The [naturality theorem](../../core/Math/EULER_NATURALITY.md)
proves semantic descent and the graded chain rule without a jet-order cutoff.
Existing custom actions can use `Mixed.ofInvariantDensity` with action-side
compatibility data. Coordinates and default selected bases can be noncomputable;
this is not a universal finite normal-form solver.

- [API and use](../../../../topics/lagrangian-model-connections/input-guide.md).
- [Model packages](../../../../../Math/RepresentationTheory/Lagrangian/LagrangianModel.lean).
- [Symmetry theorem](../../../../../Math/RepresentationTheory/Lagrangian/LagrangianSymmetry.lean).
- [Actual Yukawa model](../Physics/SCALAR_WEYL_YUKAWA.md).
- [Artificial controls](../../../../../Math/RepresentationTheory/Lagrangian/LagrangianModelControls.lean).

- [Invariant density input](../../../../topics/euler-naturality/input-guide.md).
