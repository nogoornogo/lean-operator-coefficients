# SU(6) Protection Without Strict UV Commutation

- ID: `su6-twisted-protection`
- Status: deferred (SU(6) exploration stopped by user decision, stage 01)
- Result type: proved covariant interfaces and conditional scalar/block qque obstruction;
  no protecting model constructed
- Working branch (historical): `proof/su6-twisted-protection` (deleted after integration)
- Integration target: `master`
- Integration evidence: merged into `master` by `checkpoint 01` at stage 01,
  after explicit user authorization; documentation checkpoint `checkpoint 02`.

## Stopping Decision

The user ended further SU(6) model exploration at stage 01. The verified
conditional scalar/block obstruction is retained; a protecting model was not
constructed. See [closure and scope](closure.md) for the outcome and deferred
questions. The reader-facing [model study](../../model-studies/su6-protection/README.md)
is separate from the current main theorem; this topic retains work records.
Its proof sources and reusable interfaces remain intact.
Reopening the search requires a new explicit scope decision.

## Endpoint And Frozen Scope

Test whether relaxing strict UV commutation in the original finite SU(6) model
permits symmetry prohibition of dimension-six Delta-B-one coefficients.
Preserve finite-dimensional continuous-unitary matter, the original mass/index
conditions and positive SM dual target. That index does not assert an exact
full spectrum. Quantum exactness is external; no decay rate is claimed.

The initial two-route [assessment](assessment.md) was followed by explicitly
authorized interface, exterior and sequential candidate tests. Each phase has
its linked frozen plan below. No general SU(6) automorphism or non-split-extension
classification, vacuum dynamics, matching, numerical simulation, new dependencies
or conversion of an internal signature into a generated interaction is included.

## Implemented Results

- [Initial assessment](assessment.md): homomorphic inner-lift factorization and
  conditional standard-block proton-signature neutrality. Its source/charge
  certificates are not automatic consequences of an arbitrary radical index.
  See [initial inspection](initial-verification.md).
- [Covariant interface](interface.md), [plan](implementation-plan.md): genuine
  residual covariance, fixed vacuum and invariant symmetric mass; radical
  preservation and Hom descent derived. Positive/resolved targets are supplied
  application certificates. Checkpoints: `checkpoint 03`, `checkpoint 04`.
- [Exterior/support bridge](exterior-result.md), [plan](exterior-plan.md):
  all-degree exterior covariance and two-sided descent of independently defined
  supported coefficients, specialized to actual light fields at degree four.
  Checkpoint: `checkpoint 09`.
- [Exact reversing probe test](candidate-result.md), [plan](candidate-plan.md):
  actual SM phase-i dual character excludes the specified reversal behavior
  under the positive target and gauge-cover dictionary. Checkpoint: `checkpoint 05`.
- [Pointwise gauge comparison](remaining-result.md), [plan](remaining-plan.md):
  arbitrary pointwise gauge factors disappear on local coinvariants; genuine
  gauge-equivalent actions have equivalent invariant coefficients. Transfer is
  specialized to original supported four-field inputs. Checkpoint: `checkpoint 06`.
- [Invisible defect and conjugated reversal](defect-result.md),
  [plan](defect-plan.md): exact field-level multiplication defect and iff
  criterion; normalized invisible defects give a commuting local representation.
  The SM probe exclusion extends to inverses up to conjugation in K.
  Checkpoint: `checkpoint 07`.
- [Index compatibility and ambiguity](compatibility-result.md),
  [plan](compatibility-plan.md): a positive target must preserve its whole dual
  index under beta, giving a general mismatch test. An actual 15/45-dimensional
  SM gauge-spectrum pair proves equal index does not identify the full spectrum.
  Checkpoint: `checkpoint 08`.
- [Concrete-input audit](input-audit.md): source inspection confirms that the
  candidate, mass/VEV relation, full light dictionary and physical Lorentz/BNV
  support are uninstantiated application inputs. Acceptance gates are recorded;
  no new mathematical nonexistence result or protecting model is asserted.

- [Concrete Weyl-exchange candidate](weyl-candidate-result.md),
  [plan](weyl-candidate-plan.md): the actual signed `(3 6)` representative
  satisfies w^4=1 but fails fixedness of the explicitly chosen 5+1 adjoint
  vacuum. More generally its diagonal-vacuum fixedness iff exchanged
  eigenvalues agree is proved. This specific candidate is rejected at the
  vacuum gate, without constructing a full protecting model.

- [Diagonal Weyl classification](weyl-classification-result.md),
  [plan](weyl-classification-plan.md): arbitrary finite permutations with
  unit diagonal phases preserve a diagonal vacuum iff they preserve all
  eigenvalues. The preserving permutations form a subgroup. For a
  nondegenerate 5+1 split, preservation iff the sixth coordinate is fixed.
  This is specialized to supplied actual SU(6) representatives.

- [Paired-adjoint candidate](paired-adjoint-result.md),
  [plan](paired-adjoint-plan.md): copy exchange compensates the `(3 6)`
  generator; fourth-power consistency and paired-vacuum fixedness are proved.
  A constructed signed color-block SU(6) element fails to fix the second VEV,
  rejecting this specified standard-color candidate before matter/mass work.

- [Standard-block C4 phase candidate](block-phase-result.md),
  [plan](block-phase-plan.md): exact component checks pass the selected vacuum,
  group-order, mass and light-spectrum gates, but all 24 nonzero terms of the
  one-generation Lorentz/Grassmann qque contraction survive. This specified
  action fails to prohibit qque. Computational checks, not new Lean theorems.

- [Nonliftable UV C2 candidate](nonlift-result.md), [plan](nonlift-plan.md):
  no homomorphic SU(6) lift exists for the specified UV inner automorphism.
  Compensating dual-six phases give a genuine matter action and invariant mass,
  but physical qque survives. Its automorphism restricted to SM is identity.
  Exact finite checks; no new Lean theorem or protecting model.

- [Scalar/block generalization](generalization-result.md),
  [plan](generalization-plan.md): conditional nonzero physical qque exterior
  coefficient on participating actual zero modes, for standard-placement
  pointwise scalar/block factors with a genuine finite Abelian matter action.
  No homomorphic UV lift is required. All verification gates passed.

No protecting inhabitant or full physical coefficient classification is
constructed. The C4 calculation supplies an explicit finite light dictionary
and surviving physical qque contraction, without a new formal model certificate.
Commuting with the unbroken group K is not the original hypothesis of commuting
with all UV SU(6).

## Verification

[Earlier checkpoints](checkpoint-verification.md) and the linked phase results
retain their original build and audit evidence. The C4 and nonliftable UV C2
scripts retain their exact computational scope, without Lean model instances.
The [generalization result](generalization-result.md) records the new formal
endpoint and its verification separately. Pins and audit allowances are unchanged.
The user authorized master integration at stage 01. See
[integration verification](integration-verification.md).

## Deferred Scientific Questions

The [standard-placement scalar/block phase](generalization-result.md) reaches
a verified conditional nonzero qque theorem. Its
fixed class does not include arbitrary UV compensators or light placements.

Defects visible on fields obstruct the particular removed field action, while
its projected action still exists. This does not exclude all non-split models.
An arbitrary UV compensator need not preserve the radical/support or lie in K.

The necessary all-probe index test is available, but the positive gauge index
alone cannot supply a full light dictionary: charged vectorlike pairs can be
invisible to it. An actual model must exclude or include them explicitly.

See [the input audit](input-audit.md) for remaining conditions and gates.
The Weyl and paired-adjoint candidates failed their vacuum/embedding tests;
the standard-block C4 and nonliftable UV C2 candidates pass their selected
component gates but leave physical qque invariant. Their results above record
the exact boundaries, including UV versus SM liftability.

Any future candidate would need to supply a genuine action with a different relevant
coefficient action, its actual light/SM dictionary and Lorentz/BNV support;
then the residual Hom must be computed. General automorphism or extension
classification would require a new theorem-level endpoint. No such premise
is inferred from the conditional tests.
