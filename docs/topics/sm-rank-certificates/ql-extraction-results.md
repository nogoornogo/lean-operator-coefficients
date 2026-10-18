# Existing q/l support through conditional character extraction

This is the user's original second endpoint: decide the retained `Allowed(T)`
within the existing scalar cyclic q/l residual-action class. That endpoint must
not be replaced by local gauge/Weyl support alone or by a claim about arbitrary
residual groups. The [plan](ql-extraction-plan.md) freezes this consumer.

## Existing unconditional residual separation

`QLFiniteSupport` proves, for every positive cyclic order k and q,l in ZMod k,
that the actual source residual action is the scalar cyclic character of the
sum of signed species charges. The Higgs residual action is trivial. Hence

    Allowed(T(q,l,p,m,delta)) iff
      total q/l charge(p) = 0 and Allowed(LocalTest(p,m,delta)).

This scalar separation is already an unconditional Lean theorem. It includes
all contents and does not depend on a guessed residual invariant basis.
`SMQLFullKernel` previously replaced the local term by the exact actual
finite-matrix rank predicate, without literature premises. Therefore the
existing q/l residual part was not awaiting a new residual-classification
foundation; numerical rank evaluation and other residual classes were the
separate boundaries.

## Completed extraction consumer

[SMQLCompactMultiplicity](../../../Physics/StandardModel/Operators/SMQLCompactMultiplicity.lean)
combines the proved scalar separation with the constructed compact model,
continuity and integer character presentation in the
[local extraction result](compact-extraction-results.md). Only the explicit
Weyl reduction specialization remains a mathematical input.

`test_allowed_iff` proves, for every retained test:

    Allowed(T(q,l,p,m,delta)) iff
      total q/l charge(p) = 0 and multiplicity(p,m,delta) > 0.

`original_allowed_iff` proves on the actual full-field coefficient space:

    Allowed(original(q,l,p,h,d)) iff
      total q/l charge(p) = 0 and
      exists m in Fin(N_p+1),
        Admissible(h,d,m) and multiplicity(p,m,h-d) > 0.

`original_forbidden_iff` is the negation of the same predicate. The original
consumer needs Weyl reduction only for the bounded constituent tests at the
specified h-d, not for an unbounded unspecified family. Hypercharge is retained
in the extracted constituent action, and the earlier explicit charge theorem
remains available. Statistical sources, zero/empty contents, all Higgs degrees
and mixed chirality use the same uniform theorem.

No residual `Allowed(T)` or local invariant-Hom predicate is left in these
right-hand sides. No extra q/l residual premise is supplied. The exact
finite-predicate support characterization for this existing class is complete
under the authorized Weyl literature-input boundary.

## Boundaries

The spectral integer polynomial and its extracted multiplicity are
noncomputable constructions. This proof does not evaluate each content or
produce an executable allowed/forbidden classifier, numerical all-content
rank table or regenerated 572-assignment list. Those are separate consumers.
The external Weyl reduction remains an unproved theorem parameter in Lean.
Other residual representations/classes are not classified. No new CSV values,
dependencies, custom axioms, `sorry` or matching/rate assertions are introduced.

Persistent audit: `AuditSMQLCompactMultiplicity`.
See [verification](verification.md) for the conditional proof checks.
