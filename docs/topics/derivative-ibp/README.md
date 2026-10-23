# Derivatives And Integration-By-Parts Extension

- ID: `derivative-ibp`
- Status: completed; integrated into master and reverified
- Result type: direction-covariant scalar/mixed IBP, common linear EOM, scalar, left/right Weyl and free Abelian consumers, mixed kernel presentation and formal adjoint
- Working branch: `proof/derivative-ibp`
- Integration target: `master`; explicitly authorized and integrated
- Authorization: autonomous scalar, A/B and C/D/E implementation through their frozen contracts; no estimate stop between D and E
- Integration evidence: all recorded children, including nonlinear EOM, gauge/engineering and formal first variation, merged through their parents into `master`; see [master integration](master-integration.md).

## Endpoint And Scope

The [scalar contract](implementation-plan.md) and [A/B contract](mixed-implementation-plan.md)
are followed by the [C/D/E contract](direction-lorentz-eom-plan.md).
Actual unbounded scalar and mixed Bose/Fermi jets now carry internal linear
and derivative-direction actions. Currents transform with the directions;
the actual divergence range yields inverse equivariant coefficient descent.

The physical specialization uses the existing SL(2,ℂ) and Weyl actions in
Pauli coordinates with signature `(+,-,-,-)` and an explicit dual derivative
convention. Scalar contractions and Weyl derivative transformations are proved.
The free massless scalar equation includes every derivative descendant and
has a proved generator-quotient/free-algebra presentation. Its actual EOM/IBP
source has inverse, equivariant comparison with the combined off-shell quotient.

These are exact algebraic statements. Dependency pins stay fixed. Global
mixed/on-shell direct-sum decompositions, analytic integrated actions,
amplitude equivalence and full EFT counts are not asserted.

## Deliverables And Results

1. [Scalar jets/IBP](../../proof/current/core/Math/SCALAR_JET_IBP.md): ordinary
   derivatives, finite grades and a complete quadratic quotient of dimension one.
2. [Internal-linear and mixed jets](../../proof/current/core/Math/MIXED_JET_IBP.md):
   actual exterior/polynomial source, inverse grade/degree-zero bridges and a
   complete Pauli-cancelling quadratic quotient of dimension one.
3. [Direction and EOM sources](../../proof/current/core/Math/DIRECTIONAL_JET_EOM_IBP.md):
   symmetric-power coordinates, combined actions, covariant currents, actual
   EOM presentation and inverse EOM/IBP source/representation equivalences.
4. [Lorentz and massless scalar consumers](../../proof/current/core/Physics/LORENTZ_SCALAR_EOM_IBP.md):
   actual Pauli/Weyl connection, scalar metric contractions, all trace
   descendants and nonzero higher jets of arbitrary order before IBP.
5. The complete one-direction EOM regression reduces the old quadratic
   quotient from dimension one to zero. The four-dimensional kinetic term
   is an actual divergence modulo EOM; higher jets are not truncated.
6. Persistent strict audits, aggregate registration, assumptions/source
   reconciliation, full build and structural/documentation gates.
7. The integrated [linear-system/Weyl package](../linear-eom-weyl/README.md)
   recovers scalar equations, constructs actual mixed on-shell algebras and
   EOM/IBP source equivalences, and proves the free left-Weyl covariance and
   higher-jet controls.
8. Its integrated [kernel and conjugate extension](../jet-eom-completion/README.md)
   proves the exact mixed EOM kernel ideal, a complete four-dimensional
   positive-order single-field null IBP source, and actual right-Weyl and
   paired adjoint compatibility with derivatives and the linear IBP quotient.
9. The integrated [free Abelian field-strength package](../abelian-field-strength/README.md)
   proves actual antisymmetry/Maxwell/Bianchi covariance, full descendant and
   wave relations, two independent transverse jet families before IBP, and
   symmetric-algebra kernel and inverse equivariant EOM/IBP descent.

## Remaining Boundaries

The retained C/D/E contract is bounded to direction covariance, the actual
algebraic spin action and free massless scalar EOM. The integrated children
extend the parent to common linear systems, free left/right Weyl equations
with an algebraic source adjoint, and source-free Abelian Maxwell/Bianchi
relations. Massive, interacting or sourced equations, non-Abelian curvature
and gauge-covariant commutators, potential/gauge exactness, disconnected Lorentz
actions, a topological covering classification, analytic dynamics, classical
field-index and momentum comparisons, physical amplitudes and general EFT
counts remain separate work.
No new extension starts at this integration stop.

The [extension assessment](extension-assessment.md) retains the original
relative estimates. They were planning allowances rather than measured
calendar costs. D was followed directly by E as authorized.

## Verification And Sources

The [verification record](verification.md) distinguishes the retained scalar
and A/B baselines from the C/D/E checks. The new Math audits contain 112 and
94 strict transitive checks and reject Physics/GUT imports. The physical
consumer audit has 67 checks and rejects GUT imports. Only the standard axioms
are allowed. Full `lake build` passes 7612 jobs; layout passes 2118 modules.
The old proofs and audits remain intact. The authorized successful stop is reached.

- [C/D/E implementation contract](direction-lorentz-eom-plan.md).
- [Literature, library sources and reconciliation](references.md).
- [Lean library survey](library-survey.md) and [initial assessment](survey.md).
- [Verification](verification.md).
- [Dependency integration and child-branch exception](dependency-integration.md).
- [Bounded conversion stop](conversion-stop.md), [compatibility repair](compatibility-repair.md)
  and [carrier/projection connection](carrier-pilot.md).
- [Derivative-free foundations](../derivative-free-completeness/README.md).
- [Relation completeness](../../proof/current/core/Math/RELATION_COMPLETENESS.md).
- [Workflow](../../architecture/WORKFLOW.md).

The separately tracked [jet/finite-group spurion connection](../jet-spurion-evaluation/README.md)
is integrated and reverified in this unmerged topic. It retains the scalar
EOM/IBP and mixed off-shell sources while proving finite-group evaluation
and degree bounds on their local-invariant coefficients.

The [linear-system/Weyl child](../linear-eom-weyl/README.md), including its
[kernel/conjugate child](../jet-eom-completion/README.md), is integrated with
preserved history and reverified here. That integration gate passes 625 strict
checks and the 7637-job full build; details are in the
[verification record](verification.md). The retained C/D/E counts above describe
their original proof endpoint.

The [free Abelian field-strength child](../abelian-field-strength/README.md)
is also integrated with preserved history and reverified here. The enlarged
merged-state gate passes 737 strict transitive checks and the 7643-job full
build. Its own contract and [parent verification](verification.md) retain the
free Abelian source, convention and physical-comparison boundaries.

The verified [nonlinear EOM and formal gauge child](../nonlinear-eom-gauge-jets/README.md)
extends polynomial EOM/IBP, associative covariant derivatives and a formal matrix
Yang–Mills consumer under its own contract. It remains unmerged into this parent;
its separate verification does not replace the integration baseline above.

## Final Scope And Master Integration

The user accepted the recorded theorem endpoints as complete and explicitly
authorized master integration. Polynomial interacting EOM, formal non-Abelian
connections, internal-unit gauge covariance, trace IBP, engineering-degree
results and normalized scalar/matrix first variations are now included through
their bounded children. Earlier boundary and unmerged descriptions above refer
to their original checkpoints. See [final merged-state checks](master-integration.md).

Input-interface parity with the derivative-free framework and usability work
are separate topics, not unfinished proof obligations here. General Lagrangian
input adapters, analytic actions, quantum equivalence, general EFT counting
and higher-order field-redefinition equivalence remain outside this endpoint.
No further theorem extension begins as part of this integration.
