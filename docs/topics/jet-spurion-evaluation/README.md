# Jet And Finite-Group Spurion Evaluation

- ID: `jet-spurion-evaluation`
- Status: completed; integrated into the derivative/IBP parent
- Result type: actual jet coefficient evaluation and bounded spurion witnesses
- Working branch: `proof/jet-spurion-evaluation`
- Integration target: `proof/derivative-ibp`
- Authorization: new branch, planning and autonomous implementation
- Parent exception: bounded child of the unmerged derivative/IBP topic; no master integration is authorized
- Integration evidence: merged with --no-ff into proof/derivative-ibp and reverified; historical child name retained

## Endpoint And Scope

Connect [finite-group spurion evaluation](../finite-group-spurion-evaluation/README.md)
to the actual derivative sources from [derivative/IBP](../derivative-ibp/README.md).
At each fixed finite field/derivative grade, handle an arbitrary local group
and a commuting finite residual internal group, including the actual scalar
EOM/IBP quotient and off-shell mixed Bose/Fermi IBP quotient. Constant spurions
have no spacetime derivatives. Evaluation at every specified value must attain
all local-invariant, stabilizer-invariant coefficients on these actual sources.
Retain the orbit-size-minus-one and group-order-minus-one spurion degree bounds.

The [frozen plan](plan.md) specifies the actual product actions, finite
quotients, inverse coefficient transport, nonzero derivative example and stops.
The physical specialization includes the existing four-dimensional massless
scalar/Lorentz construction. The complete nonzero example uses the already
proved one-direction mixed source and a nontrivial two-element residual action;
it does not claim a four-dimensional invariant-basis classification.

## Deliverables And Acceptance

1. Product/local/residual action bridge with inverse coefficient evaluation.
2. Actual finite scalar EOM/IBP and mixed IBP consumers, with proved stability,
   commutation and finite-dimensionality rather than supplied premises.
3. Orbit and uniform spurion-degree bounds at every value, zero/nonzero criteria
   and explicit evaluation on original source representatives.
4. Nonzero mixed derivative quotient with a two-element sign action; zero-value
   prohibition and nonzero-value degree-one witness, with a degree-zero control.
5. Persistent strict audits, aggregate/layout registration, full build,
   documentation/assumption/source reconciliation and a verified commit.

## Work And Open Obligations

The frozen endpoint is proved. The common inverse coefficient bridge, actual
finite jet consumers and nonzero sign-spurion example pass their persistent
audits and full aggregate build. No implementation obligation remains inside
the contract. The [results](results.md) state the remaining mathematical and
physical boundaries. Parent integration is complete; master integration and push are not performed.

## Result And Verification

The sufficient degree bounds remain `orbitSize(s)-1` and `|H|-1` after actual
EOM/IBP and local descent. The complete mixed derivative example has sharp
degree one. The four-dimensional scalar consumer uses the proved actual
Lorentz action and massless equation. See [results](results.md) for statements
and [verification](verification.md) for 97 strict checks, the successful
7618-job full build and documentation gates. The parent baseline is retained.

## References

- [Plan and stopping conditions](plan.md).
- [Proved result and scope](results.md).
- [Source register](references.md).
- [Verification](verification.md).
- [Workflow](../../architecture/WORKFLOW.md).
