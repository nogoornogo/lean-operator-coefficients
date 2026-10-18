# Automatic Polynomial Coupling Certificates

## Supported Construction

The author supplies the existing compositional coupling structure, finite
incoming/outgoing bases, coordinate polynomials p_j and q_k, a coordinate
domain and supplied flavor identifications. The fixed kernel is still
V(y) composed with T composed with U(x). No claim that every generation
law has this structure is made.

[PolynomialBasisCoordinates](../../../Math/LinearAlgebra/PolynomialBasisCoordinates.lean)
constructs the actual coupling vectors by polynomial evaluation in the bases.
`coordinate` proves their exact basis coordinates. `expansion` derives the
bilinear residual expansion with weights p_j*q_k. This is shared mathematics,
independent of dipoles and physical matching.

[DipolePolynomialAutomation](../../../Physics/StandardModel/Operators/DipolePolynomialAutomation.lean)
provides the author-facing constructors:

- `register`: evaluates the coordinates and registers the resulting complete
  coefficient map on the specified coordinate product. No infinitude premise.
- `residual_expansion`: derived basis paths and product-weight equality for
  every input, not merely equality after selecting a flavor component.
- `certificate`: automatically supplies paths, product weights, domain equality
  and expansion proof to the existing PolynomialCertificate. The caller supplies
  only the infinitude of each independent coordinate set in addition to the
  model construction data.
- `selected`: calculates the two selected composed channel values exactly.
- `exists_nonzero_iff`: exposes the certificate's grouped-coefficient existence
  criterion, retaining the infinite-coordinate conditions.

The automation is a proof-producing constructor, not a tactic that guesses
a physical matching law, discovers arbitrary nonlinear functions to be
polynomial, selects a basis or decides every symbolic nonzero condition.
It removes manual path/weight/certificate assembly. Authors still decide
which admissible inputs and nonzero hypotheses describe their model.

## Correlations And External Coefficients

Both polynomial families use the same free coordinate type. They need not be
independent coupling coordinates: equal polynomials, shared variables, nonlinear
powers and identically cancelling paths are allowed. Only the underlying
coordinate product used for the existence theorem must have infinite sides.
The full arbitrary-input registration API is unchanged.

`PolynomialCertificate.withCoefficients` in the
[model interface](../../../Physics/StandardModel/Operators/DipoleModelInterface.lean)
transports any expansion certificate to `Registered.withCoefficients F hF`.
Its residual law, domain, paths and weights are preserved. The supplied hF
remains the explicit model-author correspondence obligation; it is not
deduced by the certificate transport.

Registration on finite coordinate sets is possible, but the infinite-product
existence theorem is unavailable unless its premises are proved. Additional
constraints can still be expressed with restrict/pullback; the automatic
certificate cannot silently be reused as an existence statement there.

## Compiled Controls

[Examples](../../../Physics/StandardModel/Operators/DipolePolynomialAutomationExamples.lean)
construct certificates with no caller-supplied expansion proof:

1. Shared scalar parameter, incoming coordinate z squared and outgoing z:
   automatic product weight gives z cubed. A nonzero grouped coefficient
   proves a nonzero admissible input exists.
2. Attach an explicitly written existing coupling generator using its proved
   correspondence, transport the automatic certificate and preserve nonzero
   realization via the registration equivalence.
3. Two equal incoming coordinates feeding a difference coupling map: the
   full selected pair is zero. The automatic certificate proves all grouped
   coefficients vanish, including cancellations across the derived basis paths.
4. Restrict the cubic construction's coordinate domain to the singleton zero:
   registration still works and no admissible nonzero input exists. The
   infinite-coordinate assumption is not supplied or bypassed.

These controls are algebraic, not physical UV matching examples. No old
numerical/model scripts were rerun; their definitions and inputs are unchanged.

## Verification And Scope

- Planning commit: `checkpoint 01`.
- `lake build Physics.StandardModel.Operators.Audit.AuditDipolePolynomialAutomation`:
  passed, 3558 jobs; no warnings in the final focused build.
- [Persistent audit](../../../Physics/StandardModel/Operators/Audit/AuditDipolePolynomialAutomation.lean):
  18 strict transitive axiom checks, only propext, Classical.choice and
  Quot.sound; model-layer imports rejected.
- `lake build`: passed, 5928 jobs; existing warnings replayed, none in the
  new source files.
- `node tools/docs/check-links.mjs`: passed, 328 Markdown files, 2010 local
  inline links, 33 heading fragments and zero errors.
- `git diff --check` and staged diff check: passed.
- `node tools/layout/check-layout.mjs`: passed, 875 modules.
- Lean LSP MCP unavailable; source inspection and CLI diagnostics used.
- An initial external-example conversion exceeded the default kernel limit.
  The final proof uses the existing registration nonzero-transport theorem;
  no kernel/resource limits were raised, and the focused build passes.
- No dependency/pin changes, custom axioms, `sorry` or audit exceptions.
- No merge or push. The unmerged model-interface parent remains the target.

The frozen automation endpoint is closed. Fixed propagators and finite
coupling bases are part of this construction. Conjugate, rational or
logarithmic coordinate functions are not presumed polynomial, and neither
physical matching/RGE nor a photon amplitude is derived. The complete
chiral B/W classification and its previous physical boundaries are unchanged.
