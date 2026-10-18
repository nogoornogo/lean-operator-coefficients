# Generator Statistics: Verified Common Layer

The generic finite-local-basis theorem now computes exchange matrices directly
from local contractions and probes. If `p_m(v_i) = delta_mi`, its matrix entry is
`p_m(localExchange_j(v_i))`. Coordinate extraction of a pulled-back coefficient
is this matrix applied to residual coefficients pulled back on flavor inputs.
This compatibility is proved from local completeness, not assumed as a
constraint-space equivalence.

## Conventions And Scope

- Operators on coefficients use forward pullback. For general group elements
  this is contravariant; no unproved left-action convention is imposed.
- A generator satisfies `action_j(f) = sign_j * f`. A bosonic exchange has
  sign +1 and a fermionic exchange sign -1.
- Local and flavor exchanges are equivariant maps for their independent groups;
  this explicitly enforces their commutation with gauge/residual actions.
- The generic theorem permits arbitrary generator index sets and signs. To
  identify these with all equations for a permutation group, a consumer must
  prove generation and the appropriate relations. That obligation is not hidden.
- Local contractions/probes are a supplied *proved* finite classification.
  Residual group and flavor multiplicity have no dimension or topology premise.

## Consumers

[Weinberg](../../../Physics/StandardModel/Operators/WeinbergPermutationCompleteness.lean)
uses the weak and spinor swap together. The local normalized line has eigenvalue
-1; combined with fermion sign -1 this gives symmetric flavor coefficients.
The generator sector is identified with the existing independent exchange
sector, and the resulting symmetric-square Hom equivalence agrees with the
existing map. The source-sector comparison reuses the old
`exchange_iff` lemma as well as the new compatibility theorem; it does not
replace the independent mixed exterior/symmetric realization proof.
The physical `WeinbergModelSector.homEquiv` now uses the new construction,
with agreement of both forward and inverse maps.

[Six-quark typed exchanges](../../../Physics/StandardModel/Operators/SixQuarkFlavorCoordinates.lean)
now use the common injective-reconstruction relation theorem in
`typed_statistics_iff`. It retains separate heterogeneous flavor arguments and
uses the existing, independently computed `reconstruct_transform` matrices.
The physical sixth-exterior/residual-Hom endpoint transitively uses this common
pointwise criterion. This chosen route avoids a new flattening of heterogeneous
multilinear flavors into a finite tensor-factor module; it preserves the existing
dimension premises and full extraction/assembly formulas.

The [six-quark local permutation equivalence](../../../Physics/StandardModel/Operators/SixQuarkPermutationCompleteness.lean)
now restricts the independent 25-coordinate classification using the common
generator-sector theorem. The four-generator condition is proved equivalent
to the full within-species sign rule using the certified permutation-word
cover. Both directions agree with the existing two-probe classification.
The scalar local result does not collapse arbitrary flavored Hom spaces to
two dimensions.

The [qqql exchange criterion](../../../Physics/StandardModel/Operators/QqqlExchange.lean)
now derives its necessary and sufficient local equations through the same
injective-reconstruction theorem. Its independent color sign and weak/Weyl
exchange matrices are preserved. The four-family endpoint transitively uses
this criterion. qque and duue additionally prove compatibility of explicit
residual actions with slot pullback and restrict coordinates through the common
statistics theorem. duql is the empty-generator specialization. The whole
four-family product has explicit extraction/reconstruction factorization lemmas.

The [Delta-L-one input transport](../../../Physics/StandardModel/Operators/DeltaLOneInputTransport.lean)
now uses the generic supported-species equivalence for all ten signed species.
Forward and inverse coefficient formulas are proved definitionally unchanged.

## Acceptance And Input Transport

The four-consumer acceptance gate is complete. See
[the integration record](integration.md) for each physical endpoint and its
inverse comparison. Common field-map transport proves compatibility from
commutation, including noninvertible zero scalings in the six-quark degree
condition. Supported species transport handles Delta L one; mixed Weinberg and
ordered dipole fields retain their own domain constructors and the common
invariant transport primitive.

No coefficient/spanning premise is added to actual-field identification, and
no common exterior type is imposed on the four different realizations. The
shared result is conditional on *proved* local classifications, not a catalogue
of arbitrary operators. Stabilizer work remains a separately authorized topic.

## Ordered Dipole Specialization

[Dipoles](../../../Physics/StandardModel/Operators/DipolePermutationCompleteness.lean)
are the empty-generator specialization: there are no repeated identical fields
in either prescribed ordered B/W channel. The common generator-sector theorem
therefore imposes no extra exchange equation. Extraction and inverse agree with
the existing SM coefficient equivalence. Electron finite dimensionality remains
exactly the premise of the existing tensor-dual/Hom conversion. This empty case
is not claimed to solve the nontrivial local-matrix consumers.

## Historical Checkpoints (stage 01)

These records describe incremental checkpoints, superseded for acceptance by
the [final verification](README.md#verification).

- Focused audit build: passed (3258 jobs), 15 strict transitive checks.
- Full `lake build`: passed (6038 jobs); existing dependency warnings only.
- Layout: 985 modules; links: 349 documents, 2207 local links; diff check passed.
- Both exact six-quark scripts passed, including the 225 Grassmann monomial
  Fierz regression. Scripts supplement, not replace, the kernel proofs.
- Existing scalar one-generation and zero-multiplicity regressions rebuilt in
  the full build. Pins and audit allowlists unchanged.

Second checkpoint (stage 01): dipole and qqql proof-step consumers plus
Delta-L-one supported input transport.

- Focused audit: `lake build Physics.StandardModel.Operators.Audit.AuditStatisticalCompleteness`
  passed (3312 jobs), 23 strict transitive checks.
- Full `lake build`: passed (6039 jobs); dependency warnings replayed.
- Both extraction and inverse of the supported input transport are audited.
- The six-quark permutation-sector equivalence is still being implemented;
  it is not part of this checkpoint's claimed endpoint.

Third checkpoint (stage 01): the local six-quark permutation equivalence,
including comparison with the old extraction and inverse.

- Focused audit: passed (3313 jobs), 31 strict transitive checks.
- Layout: 987 modules; links: 349 documents, 2211 local links; no errors.
- Full `lake build`: passed (6040 jobs); existing dependency warnings only.
- `git diff --check` passed. Existing normalization definitions were not changed;
  the previously recorded exact six-quark regression remains applicable.

## Source Map

- [Generic generator restriction](../../../Math/LinearAlgebra/StatisticalCompleteness.lean)
- [Finite local factor](../../../Math/RepresentationTheory/FiniteStatisticalFactor.lean)
- [Normalized local line](../../../Math/RepresentationTheory/NormalizedStatisticalFactor.lean)
- [Strict audit](../../../Physics/StandardModel/Operators/Audit/AuditStatisticalCompleteness.lean)
