# Graded Completeness Naturality And Subgroup Monotonicity

- ID: `graded-completeness-naturality`
- Status: completed
- Result type: proved
- Working branch: `proof/graded-completeness-naturality`
- Integration target: `master`
- Integration evidence: merged into `master` at `checkpoint 01` by explicit user direction

## Endpoint And Scope

Integrate existing coefficient transports into degree-uniform naturality of
the constructed residual-quotient completeness equivalence. Construct maps
directly from field identifications and residual-group homomorphisms, then
prove compatibility with extraction and reconstruction. Prove subgroup
monotonicity of prohibition and allowance, without assuming restriction is
an equivalence.

Keep the existing non-derivative, finite-species, complex algebraic scope.
Residual groups, multiplicity modules and mixed degrees remain arbitrary;
no finite-dimensionality, compactness or semisimplicity is added.
See the [frozen plan](plan.md).

## Deliverables And Acceptance

1. Direct maps on mixed coefficient inputs and constructed residual quotients.
2. Extraction/reconstruction squares, identity and composition laws.
3. Subgroup monotonicity and surjective-group transport compatibility.
4. Support-selected and all-degree versions, bounded regression tests and
   strict audits, followed by full build and completed-result documentation.

## Work And Open Obligations

All frozen acceptance gates are met: independently constructed quotient maps,
field-change and restriction squares, inverse/identity/composition laws,
selected/all-degree interfaces and correct subgroup monotonicity. No acceptance
obligation remains. Existing completeness equivalences remain prerequisites,
not new achievements of this topic. Master integration is complete.

## Result And Verification

The strict focused audit passed 110 transitive checks; the full `lake build`
passed 6,547 jobs. Layout, Markdown links and diff checks passed. See
[final evidence](results.md). Root README and dependency pins remain unchanged.

## References

- [Results and acceptance evidence](results.md)
- [Completed-result dossier](../../proof/current/core/Math/GRADED_COMPLETENESS_NATURALITY.md)
- [General completeness dossier](../../proof/current/core/Math/GRADED_OPERATOR_COMPLETENESS.md)
- [General completeness topic](../graded-operator-completeness/README.md)
- [Consumer comparison regressions](../graded-sector-regressions/README.md)
- [Coefficient transport](../../../Math/RepresentationTheory/InvariantCoefficientTransport.lean)
- [Relation quotient](../../../Math/RepresentationTheory/RelationQuotient.lean)
- [Surjective Hom transport](../../../Math/RepresentationTheory/Decomposition/SurjectiveHomTransport.lean)
- [Flavor stabilizer results](../flavor-stabilizer/results.md)
