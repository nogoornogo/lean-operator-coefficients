# Coupling-Derived Mediator Paths

## Structural Input, Not An Assumed Decomposition

[Couplings](../../../Physics/StandardModel/Operators/DipoleCouplingModel.lean)
contains only the following data, with residual representations a, b, m:

```text
incoming  : X ->linear Hom(a,m)
outgoingB : Y ->linear Hom(m,b)
outgoingW : Y ->linear Hom(m,b)
propagator: Hom(m,m)
```

The spaces X and Y are allowed coupling spaces, not the full Wilson-coefficient
space. They can be proper coupling spaces; the three linear maps need not be
surjective or injective. Each coupling preserves the chosen residual symmetry.
Finite bases bx and by of X and Y are the only finite-expansion input.
The existence of such bases supplies finite-dimensionality; the structure
itself also makes sense for infinite-dimensional spaces.

The model uses the compositional residual kernel

```text
K_B(x,y) = outgoingB(y) composed with propagator composed with incoming(x)
K_W(x,y) = outgoingW(y) composed with propagator composed with incoming(x)
```

This is an explicit algebraic kernel law. It is not derived from symmetry
alone or identified with an uncomputed physical loop matching expression.
The generated full dipole coefficient is the inverse of the existing
independently proved coefficient equivalence applied to this residual pair.
No path list, arbitrary generation function F, factorization equality or
path-isolation hypothesis is a field of `Couplings`.

Vertex dependence is linear in the two coupling spaces separately, but
the total coefficient generation is bilinear, not a linear coefficient
family in the combined input. Arbitrary nonlinear parameterizations into
X and Y are allowed by the pullback theorem below.

## Derived Decomposition

The kernel is proved bilinear. The operator-independent
[BilinearSelectedPaths](../../../Math/LinearAlgebra/BilinearSelectedPaths.lean)
then expands it in any supplied finite bases:

```text
path_(j,k) = (K_B(bx_j,by_k), K_W(bx_j,by_k))
weight_(j,k)(x,y) = coordinate_j(x) * coordinate_k(y)
(K_B(x,y), K_W(x,y)) = sum_(j,k) weight_(j,k)(x,y) * path_(j,k)
```

`generation_factorization` proves the residual path equality for the full
generated coefficient. `basis_paths` identifies these paths with the existing
mediator interface, absorbing the fixed propagator into each incoming path.
`generation_eq_paths` proves equality of the complete generated coefficient
with the earlier path reconstruction, not just equality after flavor selection.

Consequently, the old factorization obligation is discharged for this
structural class. We have not proved that every symmetry-compatible
generation law is of this compositional form.

## Nonzero Conditions And Explicit Inputs

When x and y vary independently over their full allowed coupling spaces:

```text
exists x,y with nonzero selected generated B/W pair
  iff exists j,k with
    electron(outgoingB(by_k)(propagator(incoming(bx_j)(mu)))) != 0
    or the corresponding W value != 0
```

This is `exists_nonzero_iff_basis_path`. The basis-vector input
(x,y) = (bx_j,by_k) isolates that path, as proved by `weights_isolate`:
both coordinate functions are Kronecker deltas. No independent path-control
assumption is needed. `nonzero_at_basis_witness` gives this actual sufficient
input explicitly. The existence property is basis-independent, even though
the displayed finite criterion uses the chosen bases.

If u : Z -> X and v : Z -> Y are arbitrary, possibly nonlinear or correlated
parameter maps, `parameterized_factorization` still proves the same complete
coefficient decomposition with pulled-back coordinate-product weights.
It does not assert that basis-vector inputs are reachable from Z. The prior
arbitrary-domain or polynomial-weight criteria can be applied when their
domain and weight hypotheses are actually satisfied.

No assertion of nonzero coefficients is made merely from nonzero coupling
spaces or representation overlap. Selected compositions can vanish because
of the incoming image, the propagator or the outgoing flavor projection.
`generation_zero_of_propagator_zero` proves that a zero propagator kills the
entire coefficient, not only the monitored flavor component.

## Sample Controls

[DipoleCouplingControls](../../../Physics/StandardModel/Operators/DipoleCouplingControls.lean)
uses scalar coupling spaces, a scaled identity incoming map, a scaled
off-diagonal B bridge, zero W map and propagator t times the identity.
Lean proves that the selected pair is (x*y*t,0), with exact nonzero criterion
x != 0 and y != 0 and t != 0. For t = 0 the full coefficient is zero.
The nonlinear parameterization (x,y) = (z squared,z) with t = 1 has selected
pair (z cubed,0). These are controls, not claims about a UV model.

## Verification And Research Boundary

- Planning commit: `checkpoint 01`.
- `lake build Physics.StandardModel.Operators.Audit.AuditDipoleCouplingModel`:
  passed, 3551 jobs, no warnings in the final focused build.
- [Persistent audit](../../../Physics/StandardModel/Operators/Audit/AuditDipoleCouplingModel.lean):
  20 strict transitive axiom checks, only propext, Classical.choice and
  Quot.sound; model-layer imports rejected.
- `lake build`: passed, 5919 jobs. Existing warnings replayed; none in the
  new source files.
- `node tools/layout/check-layout.mjs`: passed, 866 modules.
- `node tools/docs/check-links.mjs`: passed, 323 Markdown files, 1976 local
  inline links and 33 heading fragments; zero errors.
- `git diff --check` and staged diff check: passed.
- Lean LSP MCP unavailable; source reads and CLI builds used. No custom
  axioms, `sorry`, dependency/pin changes or audit exceptions.
- No merge or remote push; the parent target is still unmerged.

The requested path-decomposition step is now proved for a stated compositional
coupling class. The overall research objective remains in progress: physical
matching of a target model family, or a broader generation law, is not proved.
No adjoint/conjugate coupling relation, mass-derived propagator, loop factor,
RGE, mass-basis derivation or electromagnetic combination was introduced.
These restrictions must not be dropped when interpreting the existence theorem
as a statement about actual decay amplitudes.

Under the user's subsequent clarification, physical matching is the model
author's responsibility, not the project's completion gate. The
[model-interface endpoint](../clfv-dipole-model-interface/README.md) supplies
certified registration and application of these proofs under that revised goal.
