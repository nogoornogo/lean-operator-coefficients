# Certified Interface Results

## Acceptance And External Responsibilities

The user's revised endpoint is usability of the existing algebraic proof core,
not a matching calculation for a particular UV theory. This interface meets
that endpoint for arbitrary registered generation laws, coupling pullbacks,
certified polynomial laws and finite coordinate matrices. Physical matching
is an explicit model-author responsibility, not an unfinished proof being
silently supplied as an axiom.

See the [model-author guide](model-author-guide.md) and
[compiled examples](../../../Physics/StandardModel/Operators/DipoleModelExamples.lean).
No actual model-specific loop calculation is presented as verified here.

## Interface Map

[DipoleModelInterface](../../../Physics/StandardModel/Operators/DipoleModelInterface.lean)
registers admissible inputs, supplied flavor identifications, an actual full
coefficient map and a residual pair. `correspondence` certifies equality under
the complete SM coefficient equivalence only on admissible inputs.

- `ofResidual`: reconstruct coefficients and derive their correspondence.
- `ofCouplings`: register an existing structural coupling model with arbitrary
  incoming/outgoing parameter maps, including nonlinear and correlated maps.
- `withCoefficients`: attach an existing coefficient calculation by proving
  correspondence once. `nonzero_withCoefficients_iff` preserves the conditions.
- `selected`, `nonzero_iff`, `nonzero_of_channel`: selected values and exact or
  sufficient input conditions, including admissibility.
- `forbidden_of_distinct_weights`: reuse the residual symmetry prohibition.
- `restrict`, `pullback` and their exact criteria: retain domain constraints
  rather than importing existence from an independently variable coupling space.
- `exists_pullback_iff`: a nonzero input survives precisely when a registered
  nonzero input belongs to the parameter map's actual range.

`PolynomialCertificate` bundles the actual independent-coordinate product,
its infinite-coordinate conditions, residual paths, weights and expansion.
It can be attached to any registered full coefficient law. Shared-coordinate
weights are allowed; `grouped` sums all monomial contributions in B and W.
`exists_nonzero_iff` and `no_nonzero_iff` provide exact existence/prohibition
criteria without a path-isolation assumption.

[MatrixIntertwiner](../../../Math/RepresentationTheory/MatrixIntertwiner.lean)
converts coordinate matrices with proved equivariance into residual maps.
[DipoleMatrixInterface](../../../Physics/StandardModel/Operators/DipoleMatrixInterface.lean)
registers two matrices and proves that the selector is the pair of designated
row-e, column-mu entries. Neither residual equivariance nor a physical mass
basis is assumed from an arbitrary matrix.

## Compiled Controls

The samples exercise actual application-facing interfaces:

1. Attach the preexisting nonlinear coefficient generator to a residual
   registration; prove the exact nonzero-input condition.
2. Register the structural coupling model with shared parameter z and maps
   z squared, z; selected pair is (z cubed,0), nonzero exactly for z != 0.
3. Certify a one-coordinate cubic polynomial law; prove nonzero-input existence
   via `grouped` coefficient extraction, not a surjectivity assumption.
4. Certify two opposing paths with shared cubic weight; use `no_nonzero_iff`
   to prove that all admissible selected pairs vanish by grouped cancellation.
5. Register finite B/W matrices with trivial residual action; selected matrix
   entry is z cubed and gives the same exact condition.
6. Restrict the matrix model to nonzero parameters and pull back along a
   constant-zero map; prove that no admissible nonzero input survives.

These are algebraic regression controls, not physical UV examples. No unrelated
numerical/model tests were rerun; their definitions and input data are unchanged.

## Verification

- Planning commit: `checkpoint 01`.
- `lake build Physics.StandardModel.Operators.Audit.AuditDipoleModelInterface`:
  passed, 3558 jobs; final new-source builds have no warnings.
- [Persistent audit](../../../Physics/StandardModel/Operators/Audit/AuditDipoleModelInterface.lean):
  30 strict transitive axiom checks, only propext, Classical.choice and
  Quot.sound; rejects model-layer imports.
- `lake build`: passed, 5924 jobs; existing warnings replayed, no warnings
  in the new source files.
- `node tools/docs/check-links.mjs`: passed, 326 Markdown files, 1995 local
  inline links and 33 heading fragments; zero errors.
- `git diff --check` and staged diff check: passed.
- `node tools/layout/check-layout.mjs`: passed, 871 modules.
- Lean LSP MCP unavailable; source reads and CLI diagnostics used.
- No custom axioms, `sorry`, dependency/pin changes or audit exceptions.
- No merge or remote push. All parent milestones remain unmerged.

## Remaining Boundaries

The usable algebraic interface endpoint is closed. Optional extensions include
automatic polynomial certificates for additional coupling parameterizations
and basis-aware adapters for non-coordinate representations. They are not
requirements for using the registered model API.

Adjoint/conjugate calculations, mass-derived propagators, matching/RGE, flavor
mass-basis derivation, electromagnetic matching and rates remain external.
Their absence is not evidence against the proved interface, but a registered
nonzero B/W pair must not be described as an observed decay prediction.
