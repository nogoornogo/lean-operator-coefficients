# CLFV Dipole Coupling Model

- ID: `clfv-dipole-coupling-model`
- Status: completed
- Checkpoint detail: completed (bounded compositional coupling endpoint); merged
- Integration result: [merge chain and verification](../clfv-dipole-completeness/integration.md).
- Result type: proved for the stated algebraic coupling class
- Working branch: `proof/clfv-dipole-coupling-model`
- Integration target: `proof/clfv-dipole-polynomial-inputs`
- Parent exception: bounded child of the unmerged polynomial-input topic.
- Integration policy: no merges or remote push; retain verified milestones.
- Overall research objective: see the [revised interface endpoint](../clfv-dipole-model-interface/README.md);
  physical matching is a model-author responsibility, not the completion gate.

## Frozen Structural Endpoint

Specify a compositional algebraic model by residual representations A, B, M,
finite-dimensional incoming/outgoing coupling spaces X, Y, linear maps from
X into Hom(A,M) and from Y into each of Hom(M,B), and a fixed intertwiner
T : M -> M. The residual channels are V_B(y) composed with T composed with
U(x), and likewise W. Neither a path decomposition nor a coefficient
factorization equality is a field of this model structure.

Derive bilinearity and finite path decomposition from this structural input
using finite bases of X and Y. Paths are basis-map compositions; weights are
products of the two coupling coordinates. Reconstruct the complete dipole
coefficients through the existing independent coefficient equivalence and
prove their residual path equality, rather than require it as a theorem premise.

When x and y vary independently over the full coupling spaces, prove:
nonzero selected generated coefficient exists iff one basis-map composition
has nonzero selected B or W component. Derive isolating inputs from the
actual basis vectors, not a controllability assumption. Also prove exact
decomposition for arbitrary nonlinear parameterizations into X and Y, with
no reachability assertion for a restricted parameter domain.

## Interfaces And Boundaries

- Math: finite-basis expansion of bilinear maps, derived path isolation,
  selected existence criterion, arbitrary-domain pullback.
- Physics: structural coupling data, bilinear residual kernel, complete
  coefficient reconstruction, derived basis-path factorization and criteria.
- Controls: a nonzero mediated bridge and a zero propagator; no UV sample.
- Fixed T need not be invertible, positive, Hermitian or mass-derived. X/Y
  may be proper spaces of allowed couplings; no surjectivity onto Hom assumed.
- This explicitly assumes a compositional kernel law, not a physical matching
  calculation. Symmetry alone does not imply this law or a nonzero loop factor.
- No matching/RGE, adjoint/conjugation, loop integrals, mass bases or photon
  amplitudes. No new foundations, dependency changes or audit exceptions.

Stop after proving/auditing these interfaces, focused/full builds, layout/link
checks and diff review pass, and committing the verified milestone. A failure
of the claim or a necessary physical scope change requires a recorded decision.

## Result And Verification

The coupling structure, bilinearity, derived finite-path factorization,
complete coefficient equality, explicit basis-vector nonzero inputs and
arbitrary nonlinear pullbacks are proved. See [results](results.md) for the
exact structural hypothesis and distinction from physical matching.

- Planning commit: `checkpoint 01`.
- Verified proof/result commit: `checkpoint 02`.
- Focused build: passed, 3551 jobs; 20 strict transitive axiom checks.
- Full build: passed, 5919 jobs; no warnings in the new source files.
- Layout: passed, 866 modules. Final link/diff results are recorded in results.
- Lean LSP MCP unavailable; source reads and CLI checks used.
- No dependency/pin changes, audit exceptions, merges or remote push.
- The commit-reference update is documentation-only; no Lean build rerun.
  The verified proof baseline remains `checkpoint 02`.

Path decomposition is no longer an assumed equality for this coupling class.
Identification with a physical matching law remains the model author's
responsibility. The revised interface topic supplies certified registration
and correlated-input application without treating that external duty as an
unfinished project proof.

## Sources

- [Polynomial-input results](../clfv-dipole-polynomial-inputs/results.md)
- [Mediator path interface](../../../Physics/StandardModel/Operators/DipoleMediatorPaths.lean)
- [Weighted selection](../../../Math/LinearAlgebra/WeightedSelectedPaths.lean)
- [Results and theorem map](results.md)
