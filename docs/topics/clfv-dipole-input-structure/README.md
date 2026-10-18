# CLFV Dipole Input Structure

- ID: `clfv-dipole-input-structure`
- Status: completed
- Checkpoint detail: completed (bounded algebraic endpoint); merged
- Integration result: [merge chain and verification](../clfv-dipole-completeness/integration.md).
- Result type: proved, with explicit model-factorization and isolation interfaces
- Overall research objective: revised in the [model-interface topic](../clfv-dipole-model-interface/README.md);
  this status closes only the bounded finite-path endpoint.
- Working branch: `proof/clfv-dipole-input-structure`
- Integration target: `proof/clfv-dipole-completeness`
- Parent exception: bounded child of the unmerged completeness topic; do not
  integrate its parent into `master` as a side effect.
- Integration policy: retain commits without merging, per the user's instruction.

## Frozen Endpoint

Give structural input criteria for finite weighted families of residual
intertwiners factoring through a mediator representation. For an arbitrary
input domain X, weights w : X -> (I -> complex) need not be linear. Both B
and W channels share each incoming path but may have different outgoing maps.
Use the already proved dipole coefficient equivalence to reconstruct the
complete coefficients from these residual paths.

Prove the selected coefficient equals the finite sum of selected paths.
For a fixed input, this sum gives the necessary and sufficient criterion,
including cancellations. If each path can be isolated by an actual input
(weight 1 on that path, 0 on the others), existence of a nonzero selected
coefficient is equivalent to existence of a path with a nonzero selected
composite. Isolation is an explicit sufficient controllability assumption,
not a claim about every UV model. A single active selected path gives an
explicit sufficient input criterion without isolation of the whole family.

## Interfaces And Boundaries

- General Math: weighted finite synthesis, selection, isolated-path theorem,
  one-active-selected-path criterion, and cancellation control.
- Physics: compose equivariant incoming/outgoing maps, reconstruct B/W
  coefficients, specialize the general criteria, and transport to any supplied
  generation map satisfying the stated residual factorization equality.
- Controls: cancellation of two individually nonzero paths; a nonlinear square
  weight family with isolating inputs. Controls are samples, not restrictions.
- Do not compute matching, loop integrals, RGE, masses or photon amplitudes.
  Factorization is an explicit algebraic model interface, not a derived UV law.
- No new foundational prerequisites, dependencies, axioms or audit exceptions.

Stop when these interfaces are proved and audited, focused and full builds,
layout/link checks pass, and the verified milestone is committed. A failure
of the frozen claim or a necessary scope change requires a recorded decision.

## Result And Verification

All frozen interfaces are proved. See [results](results.md) for the exact
input criteria, the optional path-isolation hypothesis and cancellation
controls. Concrete UV matching and model reachability remain outside scope.

The unmerged [polynomial-input child](../clfv-dipole-polynomial-inputs/README.md)
removes the isolation hypothesis for polynomial weights on independent
infinite-coordinate products, using grouped monomial contributions instead.

- Planning commit: `checkpoint 01`.
- Verified proof/result commit: `checkpoint 02`.
- Focused build: passed, 3549 jobs, 23 strict transitive axiom checks.
- Full `lake build`: passed, 5909 jobs; existing warnings replayed, none in
  the new source files.
- Layout: passed, 858 modules. Final link/diff results are recorded in results.
- Lean LSP MCP was unavailable; source inspection and CLI builds were used.
- Dependency pins and audit allowlists unchanged. No merge or remote push.
- The commit-reference update is documentation-only; no Lean build rerun.
  The verified proof baseline is `checkpoint 02`.

## Sources

- [Parent completeness result](../clfv-dipole-completeness/results.md)
- [Flavor selection](../../../Physics/StandardModel/Operators/DipoleFlavorSelection.lean)
- [Arbitrary input selection](../../../Math/LinearAlgebra/SelectedCoefficientInputs.lean)
- [Results and theorem map](results.md)
