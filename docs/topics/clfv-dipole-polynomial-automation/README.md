# CLFV Dipole Polynomial Automation

- ID: `clfv-dipole-polynomial-automation`
- Status: completed
- Checkpoint detail: completed (polynomial construction endpoint); merged
- Integration result: [merge chain and verification](../clfv-dipole-completeness/integration.md).
- Result type: proved constructors and automatic expansion certificates
- Working branch: `proof/clfv-dipole-polynomial-automation`
- Integration target: `proof/clfv-dipole-model-interface`
- Parent exception: bounded child of the unmerged model-interface topic.
- Integration policy: retain verified milestones without merging or pushing.

## Frozen Endpoint

Automatically construct the polynomial certificate for a compositional coupling
model when the incoming and outgoing coordinates in supplied finite bases
are specified by complex multivariate polynomials p_j and q_k. Coordinates
may share parameters. The propagator and basis coupling maps stay fixed.

Evaluate those coordinate polynomials into actual coupling vectors, register
the resulting model using the existing interface, derive paths from basis
couplings, and construct weights p_j*q_k and their expansion proof. Authors
must not supply the residual expansion equality or manually assemble the path
certificate. They still supply the structural coupling model, bases, polynomial
coordinates, flavor identifications and actual input domain.

Registration and exact selected-value calculation need no infinite-domain
assumption. Certificate-based existence and prohibition require an independent
coordinate product with infinite sides, explicitly supplied as before. No
automatic inference of polynomial dependence for arbitrary functions or
physical matching law is claimed. Arbitrary-input interfaces remain unchanged.

## Deliverables And Stop

1. Operator-independent evaluation of polynomial basis coordinates and bilinear
   product-weight expansion.
2. Registered coupling constructor, selected-value lemma and automatic
   PolynomialCertificate constructor for the admissible infinite product.
3. Compiled nonlinear/shared-coordinate and cancellation controls, and a finite
   domain control separating registration from the certificate condition.
4. Model-author usage instructions, strict persistent audit, focused/full builds,
   layout/link checks, diff review and verified milestone commits.

Stop after these four deliverables. Do not add matching/RGE, adjoint engines,
new foundations, dependencies, custom axioms or audit exceptions. All physical
scope and matching obligations of the parent interface are preserved.

## Result And Verification

All four deliverables are implemented and checked. See [results](results.md)
and the [updated author guide](../clfv-dipole-model-interface/model-author-guide.md).
No caller-supplied expansion equality is needed for polynomial coupling
coordinates in the specified finite bases. Physical matching remains external.

- Planning commit: `checkpoint 01`.
- Verified proof/automation commit: `checkpoint 02`.
- Focused audit build: passed, 3558 jobs, 18 strict transitive axiom checks.
- Full build: passed, 5928 jobs; no warnings in the new source files.
- Layout: passed, 875 modules. Link/diff results recorded in results.
- Lean LSP MCP unavailable; source inspection and CLI diagnostics used.
- Dependencies/pins and audit allowlists unchanged. No merge or push.
- The proof-reference update is documentation-only; no Lean build rerun.
  The verified proof baseline remains `checkpoint 02`.

## Sources

- [Model interface](../clfv-dipole-model-interface/README.md)
- [Bilinear paths](../../../Math/LinearAlgebra/BilinearSelectedPaths.lean)
- [Coupling model](../../../Physics/StandardModel/Operators/DipoleCouplingModel.lean)
- [Results and scope](results.md)
