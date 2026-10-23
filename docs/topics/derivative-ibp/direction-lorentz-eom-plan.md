# Direction, Lorentz And Free Scalar EOM Contract

Status: completed and verified on `proof/derivative-ibp`; successful stop reached.
Integration target: `master`; integration requires separate authorization.
This continues the completed [A/B contract](mixed-implementation-plan.md).
The user authorizes C → D → E without a separate estimate stop after D.

## Frozen Scope And Interfaces

Generators are source vectors; coefficient maps are their linear duals.
Ordinary commuting derivative symbols have no factorial normalization.
All jet orders remain available. Component bases are specified; finite
component/direction sets enter finite-grade and coordinate-sum results only.
Internal group representations remain arbitrary and separate from directions.
Dependency pins, default elaboration limits and the existing audits stay fixed.

C constructs functorial linear changes of derivative directions on the actual
multi-index jet module, connects them with symmetric powers of the direction
module, lifts them to the actual scalar and mixed algebras and proves joint
grade preservation. Derivatives and current components transform together;
divergence equivariance proves stability of its actual range. Existing source
and inverse coefficient descent must apply to these proved actions. Acceptance
includes a non-diagonal two-direction order-two calculation that fixes matrix
orientation and the binomial coefficient.

D specializes C to the actual algebraic SL(2,ℂ) action, fixes signature
`(+,-,-,-)` and the vector/derivative convention, and connects its left/right
spinor factors with the existing Weyl actions. The connected spin-cover action
is the endpoint; disconnected parity and time reversal are excluded. Acceptance
includes a four-direction invariant scalar metric contraction and an actual
Weyl derivative transformation with equivariant IBP descent. Reuse a narrow
proved or attributed interface rather than importing the entire SM jet closure.
No compactness, averaging or general invariant-ring theorem is assumed.

E treats only the free massless scalar equation `□φ=0`, including every ordinary
derivative descendant. Construct its quotient generator module and free scalar
algebra, prove shift and Lorentz stability and induced derivatives, and prove
the connection to the algebraic EOM ideal in the existing scalar presentation.
The subsequent IBP relations are the actual divergence range as a linear
submodule. Prove inverse coefficient descent for the combined quotient.
Acceptance includes the complete one-direction quadratic regression (the
previous one-dimensional off-shell quotient becomes zero), and a genuine
four-direction trace relation and its descendants, retaining traceless higher
jets. The one-direction regression alone does not complete the Lorentz/EOM gate.

Massive, interacting and Weyl EOM; gauge-covariant commutators; curvature and
Bianchi identities; integrated actions; amplitude equivalence; general EFT
counting and numerical dynamics are excluded. No new physical input or
literature completeness premise is introduced.

## Work And Acceptance Gates

1. Direction-symbol polynomial action, symmetric-power/multi-index connection,
   order preservation and covariance of generator shifts.
2. Actual scalar/mixed action, grade/source transport, transforming currents,
   divergence equivariance and inverse coefficient descent; shear control.
3. Narrow Lorentz/spinor adapter, metric preservation and scalar/Weyl consumers.
4. Derivative-closed massless scalar EOM, quotient presentation, induced
   derivatives/action and EOM/IBP coefficient equivalence; complete controls.
5. Persistent strict transitive audits, focused builds, full `lake build`,
   layout and documentation checks, assumptions/source reconciliation, diff
   review and coherent commits on this branch.

A coherent checkpoint does not stop the authorized sequence. Stop successfully
only after all gates pass. A necessary semantic bridge failing within the two
named routes (polynomial coordinates and abstract symmetric-algebra transport)
produces a documented scoped failure, not an assumed stability theorem.
Stop for a scope decision before changing dependencies, raising default limits,
adding an external premise or starting an excluded foundation. Heavy checks use
serialized builds with four Lean threads, a 16 GiB per-process memory guard and
a 540-second process timeout, matching the preceding implementation envelope.
Disposable logs stay outside source control. A resource stop must be reported
as such rather than as a mathematical counterexample.

## Implemented Endpoint

C supplies the actual polynomial-symbol/symmetric-power and multi-index jet
connection, order-preserving combined actions, equivariant mixed source and
covariant current/IBP descent. D uses a narrow locally proved Pauli adapter
for the existing SL(2,ℂ) group, with the dual derivative convention, real
Minkowski preservation, scalar contractions and Weyl transformation checks.
No equality with Physlib's coordinate map or covering classification is claimed.

E constructs the quotient generators and free scalar algebra, proves its
EOM-ideal presentation and actual derivative/action descent, and compares
EOM-then-IBP with the combined off-shell source in both directions, including
representations. The one-direction quotient is zero. In four dimensions the
kinetic term is an actual divergence modulo EOM, while pure time jets of
every order remain nonzero before IBP. See the
[mathematical result](../../proof/current/core/Math/DIRECTIONAL_JET_EOM_IBP.md),
[physical consumers](../../proof/current/core/Physics/LORENTZ_SCALAR_EOM_IBP.md)
and [verification](verification.md).

All five acceptance gates pass, including 273 strict transitive checks, full
`lake build` (7612 jobs), layout and documentation checks. No scope/dependency
change or separate estimate stop after D was needed. The topic remains
unmerged into master.
