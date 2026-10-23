# Nonlinear EOM And Formal Gauge Jets

- ID: `nonlinear-eom-gauge-jets`
- Status: completed
- Result type: proved polynomial EOM/IBP, associative curvature identities and formal matrix Yang–Mills consumer
- Working branch: `proof/nonlinear-eom-gauge-jets`
- Integration target: `proof/derivative-ibp`
- Parent exception: bounded child of the unmerged derivative/IBP topic
- Authorization: user-directed implementation of nonlinear EOM, covariant derivatives and Yang–Mills connection through the frozen stops
- Integration evidence: merged with preserved history through the recorded parents into `master`; see [master integration](../derivative-ibp/master-integration.md).

## Endpoint And Scope

Follow the [contract](plan.md): polynomial nonlinear EOM first, algebraic
connection/curvature identities second, and a formal matrix Yang–Mills consumer
third. All results concern exact formal jets and algebraic quotients. Existing
linear, scalar/Weyl and Abelian proofs and dependency pins remain unchanged.

## Results And Stop

All three contracted stages are proved: differential ideal and inverse IBP
comparison, scalar interaction and actual Lorentz transport, associative
curvature/commutator/Bianchi identities, entrywise matrix jets and the nonlinear
Yang–Mills EOM ideal. Both physical EOM algebras have surviving units. An exact
two-by-two evaluation detects a nonzero nonlinear equation that vanishes on shell.
The [result](results.md) details the finite images and physical boundaries.
The [source register](references.md) distinguishes mathematical API reuse from
physical convention guidance. No new analytic or numerical dynamics is included.

## Result And Verification

The [verification](verification.md) records 72 Math and 74 physical strict
transitive declaration checks, the 7653-job full build and repository gates.
The [mathematical dossier](../../proof/current/core/Math/NONLINEAR_EOM_IBP.md)
and [physical dossier](../../proof/current/core/Physics/FORMAL_YANG_MILLS_IBP.md)
agree with the assumption ledgers and source register. No obligation remains
inside the contract. The successful stop is verified on this unmerged child;
parent/master integration and remote updates are not performed.

The separately verified [gauge/trace/engineering child](../gauge-covariance-engineering/README.md)
proves nonconstant internal-unit formulas, actual trace IBP and a complete
scalar degree-two source. It remains unmerged into this topic. Its contract
continues to defer Lagrangian and formal first-variation derivations.

## Final Integration

The user-authorized master integration includes this completed child through
its recorded parent chain. Earlier unmerged-stop descriptions retain their
checkpoint meaning; [merged-state verification](../derivative-ibp/master-integration.md)
is the current integration evidence. The local working branch is retired.
