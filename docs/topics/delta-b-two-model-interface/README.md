# Delta-B = 2 multiplicity and actual-field interface

- ID: delta-b-two-model-interface
- Status: completed
- Result type: proved physical/actual-field classification and scalar one-generation inverse
- Working branch: `proof/delta-b-two-model-interface`
- Integration target: `proof/delta-b-two-conventional-basis`
- Branch exception: this authorized bounded child starts from the unmerged
  conventional-basis topic. Do not integrate its parent into `master` as a side effect.
- Integration was separately authorized at stage 01; see [the record](integration.md).

## Endpoint and frozen scope

Reuse the qque input convention: an explicitly supplied residual group `H`,
finite-dimensional complex up/down multiplicity representations, and equivariant
identifications of the actual participating right-handed fields with their
standard gauge/spinor models. Classify the independently defined derivative-free
six-field degree `(2,4)` invariant sector by a residual representation-theoretic
Hom space and transport the classification to those actual fields.

The model author supplies the residual action and actual-field identifications.
No vacuum or spectrum discovery, UV matching, RGE, matrix elements or rates.
Do not assume a nonzero coefficient or a decomposition equal to the desired image.
Do not assume arbitrary multiplicities preserve the one-generation dimension two.
The permutation symmetry of flavor coefficients must be proved, not ignored.

## Plan and acceptance

1. Prove species-preserving equivariant transport of the intrinsic exterior
   degree `(2,4)` sector, with both inverse identities and a nonzero criterion.
2. Define up/down standard models with residual multiplicities and the actual-field
   input package. Record explicitly the relation to the baryon grading `3B = 6`.
3. Separate gauge/spinor contractions from residual tensors for arbitrary
   multiplicities. Derive simultaneous slot-permutation constraints on the latter.
4. Identify that constrained residual space with an explicit Hom of representations
   built from the up/down multiplicities. Prove necessity and sufficiency, not only
   injectivity of contraction assembly. Specialize back to the one-generation result.
5. Transport the Hom equivalence through the supplied field identifications and
   expose an iff for existence of a nonzero invariant coefficient.
6. Register sources and persistent strict axiom audits; focused and full builds,
   layout/link checks, diff review and coherent commits. No integration without
   separate direction.

If stage 4 requires new general Schur-functor foundations, first retain a proved
finite permutation-constraint interface and record the missing prerequisite;
seek a scope decision before beginning a new foundational project.

## Work and verification

- Proved generic species-preserving transport and both inverse identities,
  independently of a contraction ansatz or finite-dimensionality assumption.
  Nonzero-coefficient existence is equivalent before and after transport.
- Defined standard up/down models carrying arbitrary residual multiplicities,
  the independent `ModelSector`, and an `Inputs` package containing only
  actual-field equivariant identifications. `onFieldsEquiv` and
  `exists_on_fields_iff` expose the actual-field endpoint. The supplied
  identifications are still obligations of the model author, not derived spectra.
- Connected actual-field ordered reconstruction to the existing normalized
  restriction/lift theorem. Reused the integral species baryon grading;
  this does not impose baryon-number invariance on a violating operator.
- Proved 25 multilinear flavor-coordinate extraction and finite-dimensional
  assembly with both inverse identities. Residual invariance is equivalent to
  flavor-tensor invariance, identified with a heterogeneous tensor-product Hom.
- Proved necessity and sufficiency of simultaneous flavor/color/Weyl exchange
  equations, and their equivalence to all species permutations on common-carrier
  tensor slots. `statisticsEquiv` classifies that independent coefficient space
  by a constrained residual Hom. See [the precise boundary](flavor-hom.md).
- Proved typed exchange constraints on the dependent `(U,D,U,D,D,D)` family,
  without identifying the species. `homLinearEquiv` and `exists_nonzero_iff`
  classify its independent flavored coefficient space. The common-carrier
  classification is now linear too.
- Scalar flavors with trivial residual action recover the existing two-probe
  inverse, and both scalar-flavor coefficient/Hom finranks equal two.
- The physical tensor-order equivalence and up/down action identities are proved.
  Physical invariance is equivalent to independent color/Weyl/residual
  invariance, with the degree `(2,4)` hypercharge product explicitly canceled.
- `sectorHom` now extracts constrained residual Hom coordinates from independent
  `ModelSector` exterior coefficients, with proved invariant and typed exchange
  laws. The extraction is linear and injective; each physical coefficient is
  nonzero iff its extracted Hom is nonzero. `onFieldsHomLinear` transports these
  results to actual fields through the supplied `Inputs` identifications.
- `liftSector` constructs the normalized exterior inverse. Degree, physical
  invariance and both inverse identities are proved. `sectorHomEquiv` and
  `onFieldsHomEquiv` classify the entire independent physical/actual-field
  sectors; their nonzero-existence criteria are iff statements.
- The trivial-residual scalar specialization has a physical two-probe linear
  equivalence, explicit inverse, and finrank two, also transported to supplied
  actual fields. No arbitrary-multiplicity or nontrivial-character dimension-two
  assertion is made. See [the exact endpoint](flavor-hom.md).
- Focused builds and strict transitive audits pass (five Math declarations and
  four Physics declarations). Existing restriction/lift linter warnings are
  replayed; no new warning is introduced. Dependency pins and allowed axioms
  remain unchanged.

Verification commands for the input/transport milestone:

- `lake build Math.RepresentationTheory.Audit.AuditSixSlotSpeciesTransport`
- `lake build Physics.StandardModel.Operators.Audit.AuditDeltaBTwoModelInterface`
- `lake build` succeeds (5962 jobs); pre-existing dependency warnings remain.
- `node tools/layout/check-layout.mjs` succeeds (909 modules).
- `node tools/docs/check-links.mjs` succeeds (339 Markdown files, 2065 local
  links, 33 heading fragments, no errors).
- `git diff --check` succeeds. No merge or remote push performed.

Verification commands for the flavored-coordinate/Hom milestone:

- `lake build Physics.StandardModel.Operators.Audit.AuditSixQuarkFlavorResidualHom Math.RepresentationTheory.Audit.AuditMultilinearInvariantHom`
  succeeds (3228 jobs; 17 Physics and 2 Math strict transitive checks).
- `lake build` succeeds (5967 jobs); pre-existing dependency warnings remain.
  No new warning occurs in the three new proof modules.
- `node tools/layout/check-layout.mjs` succeeds (914 modules).
- `node tools/docs/check-links.mjs` succeeds (340 Markdown files, 2071 local
  links, 33 heading fragments, no errors).
- `git diff --check` succeeds. No merge or remote push performed.

Verification for the typed flavor and faithful physical-extraction milestone:

- `lake build Physics.StandardModel.Operators.Audit.AuditSixQuarkFlavorResidualHom`
  succeeds (3233 jobs; 47 strict transitive axiom checks).
- `lake build` succeeds (5970 jobs). Existing dependency linter warnings remain;
  the three new proof modules introduce no warnings.
- `node tools/layout/check-layout.mjs` succeeds (917 modules).
- `node tools/docs/check-links.mjs` succeeds (340 Markdown files, 2074 local
  links, 33 heading fragments, no errors).
- `git diff --check` succeeds. No merge or remote push performed.

Final exterior-inverse and physical one-generation verification:

- `lake build Physics.StandardModel.Operators.Audit.AuditSixQuarkFlavorResidualHom`
  succeeds (3234 jobs; 72 strict transitive checks, allowed axioms unchanged).
- `lake build` succeeds (5971 jobs); existing dependency warnings remain, with
  no new warning in the changed proof modules.
- Layout check succeeds (918 modules); local link check succeeds (340 Markdown
  files, 2076 links, 33 fragments, zero errors); `git diff --check` succeeds.
- The recorded parent target remains at `checkpoint 01`, an ancestor of this branch.
  The bounded endpoint is ready for integration review. No merge or push performed.

## References

- [qque completeness and actual-field input](../qque-coefficient-completeness/README.md)
- [Conventional basis parent](../delta-b-two-conventional-basis/README.md)
- [Intrinsic six-field degree](../../../Math/RepresentationTheory/SixSlotSpeciesDegree.lean)
- [Six-field species transport](../../../Math/RepresentationTheory/SixSlotSpeciesTransport.lean)
- [Actual-field model interface](../../../Physics/StandardModel/Operators/DeltaBTwoModelInterface.lean)
- [Flavored coordinate and residual Hom milestone](flavor-hom.md)
- [Fixed one-generation classification](../../../Physics/StandardModel/Operators/SixQuarkTwoCoordinates.lean)
- [Baryon grading](../../../Physics/StandardModel/Operators/DeltaBTwoLocalOperator.lean)
