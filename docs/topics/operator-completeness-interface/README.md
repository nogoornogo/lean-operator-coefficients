# Common Operator Completeness Interface

- ID: `operator-completeness-interface`
- Status: completed
- Result type: proved bounded common statistics/transport layer with four consumers
- Working branch: `refactor/operator-completeness-interface`
- Integration target: `master`; merge authorized at stage 01; retain branch.

## Frozen Endpoint

Formalize the permutation-equivariant algebraic layer underlying the four
integrated Delta-L-one, six-quark Delta-B-two, Weinberg and dipole classifications.
Use the existing EFT permutation-basis framework as mathematical provenance,
not a claim of discovering new general invariant theory. Local gauge/Lorentz
classification remains a proved sector-specific input.
Do not claim classification of arbitrary operator dimensions or gauge groups.
Retain each endpoint's finite-dimensionality and exchange hypotheses, rather
than imposing their union on every consumer. Preserve existing public APIs.

## Revised Plan And Acceptance

1. Freeze conventions: species-local space, multiplicity representation,
   finite within-species permutation group, boson/fermion character and
   contragredient action on local coefficient tensors. Specify the independent
   source sector before constructing coordinates.
2. Prove the commuting-action completeness theorem: a local coefficient
   classification compatible with permutations induces a classification of
   statistically admissible residual-invariant coefficients. Derive exchange
   equations from equivariance, not an assumed unspecified constraint match.
3. Connect exterior/symmetric/ordered realizations to these conditions and
   prove extraction/reconstruction and nonzero criteria. Separate actual-field
   identifications, local completeness and model-specific UV generation.
4. Reconstruct Weinberg and six-quark consumers first (mixed statistics and
   nontrivial local action), then Delta-L-one and ordered B/W dipoles. Prove
   agreement with existing maps and inverses without stronger hypotheses.
5. Run focused/full builds, strict transitive audits and sign/normalization,
   heterogeneous-carrier, zero-multiplicity and scalar regression controls.

The first theorem statement must fix tensor-dual orientation and the statistics
twist; an unproved Schur-functor formula is not an endpoint specification.
Do not impose finite-dimensionality or compactness on the abstract layer
without a proved necessity. Finite-dimensional tensor-Hom dualization stays
in optional adapters where currently required.

Completion requires four consumers of the permutation/statistics theorem,
not four wrappers around existing equivalences. An explicit invertible
coordinate map is the main output, providing basis transfer where a basis is
available without demanding one on arbitrary multiplicity spaces.

Schur/Young decomposition, executable basis enumeration, derivatives, EOM/IBP
and on-shell amplitude correspondence are deferred. Later finite-dimensional
Schur decomposition may refine, but must not replace, the arbitrary-multiplicity
layer. A new foundational milestone or physical premise requires user judgment.
Stabilizer classification follows this acceptance gate as a separate topic;
it does not wait for all Schur-Weyl theory to be formalized.

## Literature And Scope

- [Li et al., JHEP 04 (2022) 140, section 3.3](https://arxiv.org/html/2201.04639v2#S3.SS3)
  motivates permutation/statistics and optional p-basis refinement. Its operator
  construction is broader than this bounded topic; finite-flavor basis calculations
  do not justify strengthening existing arbitrary-multiplicity hypotheses.
- [Henning et al., JHEP 10 (2017) 199](https://arxiv.org/abs/1706.08520)
  supplies wider operator-space/EOM/IBP context, not implementation prerequisites.

Exchange equations can retain several permutation components and multiplicities;
they need not project onto one irreducible component. Residual invariance and
permutation symmetry are commuting constraints. The residual group is supplied,
not derived from a VEV. Literature guides the proof; no literature completeness
premise substitutes for proving the claimed Lean construction.

## Initial Comparison

- Delta L one uses a dependent family of ten species, an independent supported
  exterior sector and a four-factor residual product; no finite dimensionality.
- Delta B two uses distinct up/down carriers and a supported sixth exterior
  power. The residual Hom retains typed exchange equations; finite-dimensional
  up/down multiplicities are required by its existing assembly theorem.
- Weinberg uses exterior-square leptons tensor symmetric-square Higgs, not an
  exterior fourth power. Its single Higgs is residual-trivial; no finite
  dimensionality is needed.
- Dipoles use ordered B/W tensor channels, not an exterior sector. Their Hom
  dualization requires finite-dimensional electron multiplicity. Actual UV
  generation and matching are separate inputs and remain separate.

These different coefficient domains must remain visible in the common API.
Existing unrelated uncommitted documentation changes are preserved and are
not included in this topic's commits.

## Result

The four-consumer acceptance gate is closed. Shared theorems restrict proved
coordinates by statistics, derive exchange relations through equivariant or
injective reconstruction, and transport constraints along field identifications.
Weinberg, six quarks, all four Delta-L-one families and ordered B/W dipoles use
these constructions. Extraction and inverse formulas retain the existing
normalizations and hypotheses. See [integration and input contract](integration.md)
and [the common theorem conventions](statistics.md).

The common input is a field representation equivalence and its proved transport
laws, not one coefficient-domain type or a new spanning premise. Exterior,
mixed symmetric/exterior and ordered realizations remain distinct. The flavored
six-quark connection uses the shared pointwise reconstruction theorem; no new
tensor flattening or stronger dimension assumption is needed.

No bounded acceptance obligations remain. Deferred general operator enumeration,
Schur decomposition and stabilizer work are separate topics. Closure and merge
are authorized; remote push is not. Git ancestry records integration.

### Relationship To Li Et Al.

This is not a formalization of the entire paper, nor a proof of its full p-basis
algorithm. It formalizes a shared algebraic statistics/transport layer, with
four proved consumers, inspired by the permutation framework. It complements
operator-basis construction through residual-group Hom classification,
actual-field transport and nonzero criteria, retaining arbitrary multiplicities
where the individual endpoint allows them. No defect in the paper is asserted.
Young/Schur basis algorithms, derivatives, EOM/IBP and amplitudes remain outside
this result. The next separate topic studies a specified VEV's exact stabilizer;
the present theorems still take the residual group as an input.

## Verification

The initial unverified `OperatorFieldInputs` and `OperatorCompletenessInterface`
drafts and their aggregate imports were removed during replanning. Their fragile
heterogeneous packaging did not implement the permutation layer. Only agent-created
uncommitted drafts were removed; checked proofs and existing user documentation
edits are preserved. Git does not retain the removed drafts.

Retained auxiliary tools, not the revised general theorem:

- [Constraint restriction](../../../Math/LinearAlgebra/ConstrainedCompleteness.lean)
- [Supported species transport](../../../Math/RepresentationTheory/SpeciesCoefficientTransport.lean)
- [Strict helper audit](../../../Math/LinearAlgebra/Audit/AuditCompletenessTransport.lean)

Final acceptance (stage 01):

- `lake build Physics.StandardModel.Operators.Audit.AuditStatisticalCompleteness`:
  passed (3802 jobs), 64 strict transitive axiom checks. The retained helper audit
  has 10 additional strict checks. Only `propext`, `Classical.choice` and
  `Quot.sound` are permitted.
- Full `lake build`: passed (6040 jobs); existing dependency warnings replayed.
- `node tools/layout/check-layout.mjs`: passed, 987 modules.
- `node tools/docs/check-links.mjs` and `git diff --check`: passed.
- `python3 tools/delta-b-two/species-quotient.py` and
  `python3 tools/delta-b-two/conventional-probes.py`: passed, including the
  two-probe normalization and 225 Grassmann monomial Fierz checks.
- `python3 tools/qque/audit_one_generation.py` and
  `python3 tools/qque/audit_pairwise.py`: passed (4 and 3 tests respectively).
- Explicit bosonic +1 / fermionic -1 controls are audited. Existing scalar
  one-generation and zero-multiplicity regressions rebuilt in the full build.
  Scripts supplement, not replace, Lean proofs.
- Pins, custom-axiom policy and audit allowlists unchanged. Unrelated user edits
  are excluded from topic commits.

## Sources

- [Delta L one transport](../../../Physics/StandardModel/Operators/DeltaLOneInputTransport.lean)
- [Six-quark interface](../../../Physics/StandardModel/Operators/DeltaBTwoModelInterface.lean)
- [Six-quark completeness](../../../Physics/StandardModel/Operators/DeltaBTwoFlavorBridge.lean)
- [Weinberg interface](../../../Physics/StandardModel/Operators/WeinbergSMInterface.lean)
- [Dipole SM coefficients](../../../Physics/StandardModel/Operators/DipoleSMCoefficient.lean)
- [Invariant coefficient transport](../../../Math/RepresentationTheory/InvariantCoefficientTransport.lean)
