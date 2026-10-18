# All-Degree Heavy-Fermion Elimination Plan

Status: completed; see the [result](heavy-elimination-results.md) and
[verification](verification.md).

Continue proof/dev-mohapatra-coefficient-connection from checkpoint 01; integration
target remains master without merge authorization. The user explicitly
selected all-degree elimination rather than only replacing the degree-six
computation by Lean.

## Frozen endpoint

For the declared one-N, u,d,s Hermitian action, construct an exact heavy
solution, prove its stationary equations and uniqueness, and evaluate the
eliminated action without an external-degree truncation. Keep the source
normalization dictionary conditional. Prove the needed finite Grassmann
kernel invertibility instead of assuming a diagnostic's stationary solution.
The external carrier has 36 complex Grassmann generators; no physical
momentum-dependent propagation, loops or derivative/EOM/IBP calculus is added.

## Reusable layers

1. Finite nilpotent perturbation inverse and exact quadratic elimination in
   Math: independent of model, charge, star or number of heavy components.
2. Finite exterior coefficient kernels: positive-degree entries have a
   proved nilpotence bound, using the finite generating dimension.
3. Complex-conjugating exterior anti-involution and odd-field variation
   bridge; preserve the existing carrier and aggregate/layer boundaries.
4. Connect the literal Hermitian scalar-eliminated action and all four heavy
   components. Prove stationary solution, exact action and holomorphic
   projection, then recover the earlier selected coefficient.

Do not present a generic inverse theorem, assumed invertibility or an
uninstantiated interface as completed model matching. A coherent verified
intermediate milestone is a checkpoint; the full endpoint remains open
until its concrete premises and action bridge are proved. Record a concrete
foundational obstruction if the existing APIs cannot support a bounded
implementation, without silently weakening the endpoint.

## Verification

Focused builds and persistent strict transitive audits per layer; serialized
full lake build; layout, local links and diff checks; retain the finite
Hermitian diagnostic as a cross-check, never as a Lean premise. No dependency
changes, master integration, remote push or author contact.
