# CLFV Dipole Model Interface

- ID: `clfv-dipole-model-interface`
- Status: completed
- Checkpoint detail: completed (revised usable-interface endpoint); merged
- Integration result: [merge chain and verification](../clfv-dipole-completeness/integration.md).
- Result type: proved interfaces with explicit model-author matching obligations
- Working branch: `proof/clfv-dipole-model-interface`
- Integration target: `proof/clfv-dipole-coupling-model`
- Parent exception: bounded child of the unmerged coupling-model topic.
- Integration policy: no merges or remote push; retain verified milestones.

## Revised Goal And Frozen Endpoint

Per the user's clarification, physical matching belongs to model authors,
not to the project's completion gate. Provide a usable certified interface
to the proved coefficient classification and generation criteria. Do not
report a supplied matching premise as a derived physical law.

1. Register an admissible domain, an actual coefficient map, a residual pair,
   supplied flavor identifications, and their correspondence on that domain.
   Expose selected values, nonzero inputs, symmetry prohibition and arbitrary
   domain restriction/pullback with explicit validity boundaries.
2. Supply constructors from residual intertwiners and compositional couplings.
   Coupling pullbacks may be nonlinear and correlated; no independent-input
   existence theorem may silently be transferred to their restricted domain.
3. Bundle polynomial expansion certificates on an independent infinite-coordinate
   product and expose grouped-coefficient existence criteria for registered
   models, including correlated polynomial weights and cancellations.
4. Provide finite coordinate-matrix adapters requiring proved equivariance,
   with a theorem identifying the selected coefficient with a matrix entry.
5. Add compiled end-to-end samples and a concise model-author guide specifying
   registration obligations, theorem use and unsupported physical conclusions.

Keep the current chiral, single-residual-trivial-Higgs conventions. Do not
derive matching/RGE, mass bases, rates, photon amplitudes or a general adjoint
engine. Matrix adapters use supplied flavor coordinates. Polynomial claims
retain the existing independent-domain assumptions; arbitrary pullbacks remain
supported without requiring polynomial dependence.

Stop after these interfaces and examples are proved/audited, focused/full
builds, layout/link checks and diff review pass, and the milestone is committed.
Matching is explicitly external, not a remaining implementation obligation.
No foundations, dependency/pin changes, custom axioms or audit exceptions.

## Result And Verification

Registration, coupling and arbitrary-domain pullbacks, polynomial certificates,
matrix adapters and compiled end-to-end samples are implemented and proved.
See [results](results.md) and the [model-author guide](model-author-guide.md).
Physical matching is not a remaining implementation obligation under the
user's revised goal. Additional adapter automation is optional.

The unmerged [polynomial-automation child](../clfv-dipole-polynomial-automation/README.md)
now constructs certificates from polynomial coupling coordinates in finite
bases, without requiring a model author's path-expansion proof.

- Planning commit: `checkpoint 01`.
- Verified proof/interface commit: `checkpoint 02`.
- Focused build: passed, 3558 jobs; 30 strict transitive axiom checks.
- Full build: passed, 5924 jobs; no warnings in the new source files.
- Layout: passed, 871 modules. Link/diff results recorded in results.
- Lean LSP MCP unavailable; source/CLI checks used.
- No dependency/pin changes, audit exceptions, merges or remote push.
- The proof-reference update is documentation-only; no Lean build rerun.
  The verified proof baseline remains `checkpoint 02`.

## Sources

- [Coupling-model results](../clfv-dipole-coupling-model/results.md)
- [Flavor selection](../../../Physics/StandardModel/Operators/DipoleFlavorSelection.lean)
- [Polynomial criterion](../../../Math/LinearAlgebra/PolynomialSelectedPaths.lean)
- [Results](results.md)
- [Model-author guide](model-author-guide.md)
