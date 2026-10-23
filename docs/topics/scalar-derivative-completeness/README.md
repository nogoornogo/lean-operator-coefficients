# Finite Scalar Derivative Completeness

- ID: `scalar-derivative-completeness`
- Status: completed at the user-accepted bounded endpoint
- Result type: finite completeness proofs with an unresolved C2 order-four boundary
- Working branch: `proof/scalar-derivative-completeness`
- Integration target: `proof/derivative-literature-foundations`
- Parent exception: bounded child of the closed, unmerged verification topic;
  its proved foundations are required. Child integration does not authorize a
  parent merge into master.
- Authorization: user-directed C1/C2 formalization after verification closure

## Endpoint And Scope

Prove the remaining finite C1 two-species free-scalar sectors and the C2
four-identical-scalar low-degree invariant coefficients, using actual full
EOM/IBP relations and the existing input interfaces. Follow the
[frozen plan](plan.md) in C1, C2 degree two, C2 degree four order.

C1 targets contents (1,1) at derivative order 1 and (2,2) at orders 1,2.
C2 targets four fields at orders 2,4 with actual Lorentz covariance. These
are finite completeness statements, not all-order series or full EFT bases.
Dependencies and public input definitions remain unchanged.

## Results And Stop

The three remaining bounded C1 sectors have complete actual-image and
coefficient equivalences, normalized global coefficients and dimension 1.
For C2 order two, every admitted coefficient on the entire actual Lorentz
grade vanishes. At order four, K squared survives full EOM/IBP, and the
three specified metric contractions have a one-dimensional quotient image.

The order-four full invariant coefficient basis remains unproved. The
constructed global separator fails a specific actual shear invariance
equation; exact finite group-coordinate checks do not supply the remaining
Lean source/full-relation and arbitrary-group certificates. These concrete
structural and coordinate stops are detailed in [results](results.md).
This is not a counterexample to the expected count or a paper-wide result.

The [additional verification](validation.md) passes existing and new consumer
checks, four primary-source comparisons and independent exact polynomial
diagnostics. It includes a nonzero order-two anisotropic class whose admitted
invariant coefficients all vanish, and the normalized scalar combination
from the new Cao reference. The order-four completeness stop is preserved.

The [predecessor results](../derivative-literature-foundations/extended-checks.md)
retain their original verified scope. New work is owned by this topic.
The user closed this topic at the verified scope above and authorized its
integration into the recorded parent. The remaining C2 order-four full
invariant coefficient theorem is a separate follow-up, not a result of this
topic. Integration evidence is recorded in [verification](verification.md).
The [order-four successor](../scalar-quartic-four-completeness/README.md)
now owns the complete selected invariant coefficient theorem; the present
topic retains its original accepted proof scope.

## Records

- [Plan, hypotheses and stops](plan.md).
- [Source roles](references.md).
- [Progress and verified results](results.md).
- [Verification](verification.md).
- [Additional verification contract](validation-plan.md).
- [Existing and new consumer/literature verification](validation.md).
