# Input-Side Necessary Conditions for Prohibition

- Status: completed; frozen API endpoint proved and verified and integrated
- Working branch: `proof/prohibition-input-api`
- Integration target: `master`; separately authorized merge only
- Authorization: user closed the model-verification series, authorized its
  master integration, and requested this new branch and plan.

## Objective

Turn a requested prohibition specification into auditable necessary conditions
on an already admitted field/action input. Reuse the existing all-degree
coefficient decomposition, coefficient-space symmetry-extension criterion,
selection predicates and composable specifications. Do not create another
completeness theorem or duplicate field admission with a new model bundle.

## Frozen Scope

The common input consists of the existing typed local/residual representations,
fermion/scalar species, stable specification and actual coefficient domain.
At degree (n,m), `Forbids` will name the existing Forbidden predicate on the
selected actual coefficient space. `AllForbids` quantifies all n,m. Names are
provisional; semantics are fixed. Specifications may be unions or indexed
unions; field data are reused when the requested sectors change.

Necessary conditions must retain their exact prerequisites:

- Every selected actual residual Hom factor vanishes.
- Under explicit semisimplicity of the factor source, no common irreducible
  constituent with its target is allowed; no finite-dimensionality or
  semisimplicity is inferred from a charge table.
- For a scalar-character action on a nontrivial admitted coefficient carrier,
  prohibition requires a group element detecting its total charge. Nontriviality
  must concern the carrier after local invariance and statistics relations,
  not just the raw ordered field tensor. Neutrality alone is not existence.
- If an enlarged symmetry forbids a sector which has a smaller-symmetry
  nonzero coefficient, the relevant restriction map cannot be surjective.
  This differs from preservation of all smaller-symmetry coefficients.

Zero admissible carriers, arbitrary field extensions and model-dependent
admission remain explicit. No automatic UV model search, mass/light-spectrum
classification, derivative/EOM/IBP, anomaly, matching, rate or new dependency.

## Deliverables and Stop Condition

See the [implementation plan](plan.md) and [source register](references.md).
The bounded implementation endpoint is an audited Math API for these
implications/conditional iff statements, one existing-domain Physics adapter,
and positive/negative regressions explaining the hypotheses. Stop once those
statements, documentation and checks pass; do not recursively formalize new
local nonzero witnesses for every sector or construct a protecting UV model.

If the scalar-character bridge needs a new foundational carrier theorem,
record that prerequisite and its burden before expanding scope. Finite
character/finite-dimensional cases are acceptable intermediate results, but
must be labeled and not substituted silently for the intended statement.

The user authorized autonomous implementation to the frozen stop condition.
See [results](results.md) for the implemented API and exact hypotheses, and
[verification](verification.md) for checks. Master integration was separately authorized at stage 01.

## Outcome

Implemented the input-side prohibition facade, composition and factor criteria,
explicit semisimple common-constituent constraints, scalar detection necessity
without finite-dimensionality, and actual selected restriction obstructions.
The SM consumer and bounded model/zero-domain controls pass persistent strict
audits. Model-dependent admission remains an explicit input, not an unfinished
universal-model proof obligation. See [results](results.md).

The recorded implementation stop condition is reached. No scope expansion or
new foundational project was required. The topic is integrated into master; its historical working branch is retained
in this record. See verification for the merge checkpoint.
