# Additional Verification Contract

The user requests verification of the added C1/C2 formalization, including
existing and new cases. Reuse this topic branch and its original assumptions;
the unresolved order-four completeness stop is not reopened by this audit.

## Existing checks

Recheck the C1/C2 pinned equations and run the three retained exact diagnostics.
Run the strict namespaces for the added proofs, existing derivative and
nonderivative consumers, presentation transport, reality, and helper/direct
input connections. These retain their own theorem scopes.

## New persistent consumers

- C1: instantiate the new normalized coefficients through global restriction,
  selected extraction, inverse and actual-image operations. Check species
  exchange and arbitrary transported presentations. Prove that multiplying a
  vanishing total derivative can produce a surviving class, rejecting an
  ideal interpretation of IBP.
- C2: restrict arbitrary global coefficients to the entire order-two grade,
  including helper-derived coefficients. Construct a nonzero anisotropic
  class in that grade using the four-wave separator, so coefficient vanishing
  is not misreported as vanishing of the full un-invariant quotient.
- C2 order four: test the three-contraction relations on arbitrary admitted
  coefficients and transport K squared survival through the existing helper
  input. Do not infer an invariant global separator or complete invariant
  spanning from the fixed candidate line.

## Independent diagnostics and literature

Add a standard-library exact-rational direct polynomial evaluation that does
not reuse the finite-rank implementation. Check several null/conserving
four-wave configurations, permutations and rescalings; all bounded divergence
and free-equation rows; the normalization of K squared and an anisotropic
order-two survivor. Include controls that fail when nullness or conservation
is removed. These checks are supplementary, not Lean premises.

Reinspect the existing primary C1/C2 pins. Inspect at least one independent
primary scalar EFT operator-basis reference and the previously surveyed
low-derivative subtraction limitation. Freeze version/location, conventions,
normalization and the exact comparison claim. Each source reaches its own
proved, checked or out-of-scope stop; one partial case does not end the queue.
No amplitude/operator equivalence, renormalization result, Euclidean/Lorentz
group equivalence or whole-paper verification is claimed.

## Acceptance and stops

Preserve dependencies and published interfaces. Add persistent strict whole
namespace audits and aggregate registrations for new Lean consumers. Use the
original two-thread, two-core, 16 GiB, default-heartbeat resource contract,
180-second focused / 540-second full ceilings. Finish with focused checks,
strict audits, serialized full build, exact diagnostics and repository gates,
then record results, source roles and remaining boundaries and commit.
An actual disagreement must be resolved or reported as an unresolved failure;
never weaken a test to match an output. No master merge or push is authorized.
