# Literature Recheck Through The Obtained Proofs

All six pinned cases were reinspected and tested through the supported
foundation inputs, following the [bounded contract](literature-recheck-plan.md).
No disagreement was found in the proved specializations. This does not
certify all six bases: C1–C5 retain the specific missing statements below,
while C6 retains its complete constructed polynomial contract.

The renewed tests are persistent Lean consumers in
[DerivativeLiteratureRecheck](../../../Physics/FieldTheory/Jets/DerivativeLiteratureRecheck.lean),
namespace `GUT.DerivativeLiteratureRecheck.C1` through `C6`, with a
[strict audit](../../../Physics/FieldTheory/Jets/Audit/AuditLiteratureRecheck.lean).
These use the obtained proofs rather than treating successful script output
or a paper's count as a premise. The [original comparison](../derivative-literature-comparison/results.md)
and [usage survey](../derivative-input-literature-review/review.md) remain
records of their own earlier checkpoints.

The subsequent [nonderivative input recheck](nonderivative-recheck.md)
also consumes original Bose/Fermi and finite-local coefficients through
the integrated interface, and tests nonderivative scalar and Higgs targets
in actual EOM inputs. It has its own proof and verification gate; the six
derivative-case results below retain their recorded scope.

| Case | Renewed result | Terminal scope |
| --- | --- | --- |
| C1 | An admitted off-shell coefficient is reconstructed from the actual finite rows, with values (c,-c); the on-shell coefficient is zero | One-species quadratic control certified; two-species counts remain diagnostic |
| C2 | Complete four-scalar degree-zero image of dimension 1, the specified degree-two class vanishes, degree-four candidate is invariant | Positive-degree invariant coefficient dimensions and degree-four nonzero class remain unproved |
| C3 | Paper-normalized real parameters give the exact signed relation in the generated full quotient and for every actual global SM/Lorentz coefficient | Gaugeless/Yukawa-free input and relation verified; full Warsaw basis not verified |
| C4 | All three literal raw contractions remain independent; the former raw separator is explicitly impossible as a coefficient of the new free represented input | No quotient independence, invariant completeness or count of three follows |
| C5 | Literal Pauli-current divergence is a combination of both generated Weyl EOM; all products vanish under admitted coefficients; symmetric derivative current vanishes by EOM/IBP | New on-shell relation check, with off-shell Higgs spectators; the bidirectional candidate's physical dictionary and basis remain open |
| C6 | First substitution coefficient vanishes for every generated-input coefficient; the retained second coefficient is raw nonzero at zero coupling | Complete finite polynomial test through order two; no analytic/quantum equivalence claim |

## C1 — Actual Finite Rows

Henning et al. [1507.07240v1](https://arxiv.org/pdf/1507.07240v1),
Eq. (3.11), gives the one- and two-species series used as the benchmark.
`C1.offCoefficient` decodes the certified vector (c,-c), not an arbitrary
raw evaluation; `off_values` checks its values on both actual monomials.
`on_forbidden` uses the complete relation presentation after the free
second-derivative EOM. This rechecks the off/on distinction (1 versus 0).

The independent exact script again returns (1,1,0) for content (1,1)
and (1,1,1) for (2,2), at derivative degrees 0,1,2. Their actual
multidegree/source and full relation-preimage transport remains missing.
This local stop was followed by C2.

## C2 — Zero Degree Closed, Positive Degrees Partial

Henning et al. [1706.08520v1](https://arxiv.org/pdf/1706.08520v1),
Eq. (6.3), supplies the four-identical-scalar expectation (1,0,1) at
derivative degrees 0,2,4. `C2.certified_controls` now combines the complete
degree-zero selected image in the full free quotient with the earlier
two-derivative vanishing and four-derivative invariance. The degree-zero
generator is detected by an actual globally invariant coefficient.

The exact diagnostic still gives source sizes 1/20/305, EOM/IBP ranks
0/11/235 and infinitesimal constrained dimensions (1,0,1). Complete
positive-degree invariant span, a separating four-derivative quotient
functional, full-group transport of the diagnostic and the Euclidean
metric dictionary remain unproved. One vanished representative does not
establish a zero-dimensional entire sector. This stop was followed by C3.

## C3 — Paper Signs And Full Generated Input

Grzadkowski et al. [1008.4884v3](https://arxiv.org/pdf/1008.4884v3),
Eq. (2.1), fixes the scalar density's signs. Setting gauge and Yukawa
couplings to zero gives, with real parameters and rho = H-dagger H,

\[
L_0=K+m^2\rho-\tfrac\lambda2\rho^2.
\]

`C3.density` checks this specialization against the helper with
a=-m2 and b=lambda. The variable `m2` denotes a signed real parameter;
there is no positivity assumption. `quotient_relation` and
`coefficient_relation` prove, in the full generated input,

\[
[\rho K]=\tfrac12[\rho\Box\rho]-m^2[\rho^2]+\lambda[\rho^3].
\]

This fixes the exact coefficients of the gaugeless reading of Eq. (5.3);
that equation uses schematic class terms, so their printed plus signs
are not an assertion that all omitted coefficients equal one. The
`derivative_only_iff` test states exactly when the potential contribution
may be dropped for a given admitted coefficient. It supplies no nonzero
coefficient witness or freedom to assign independent values across counts.

The actual field/dual dictionary, global covering-SM/Lorentz action,
all four generated Euler components, full differential relation equality
and inverse direct/generated coefficient maps are now available and used.
This closes those earlier input gates for this specified relation. A
complete two-operator Warsaw basis, actual-group stable finite presentation
of the five-candidate selection, local gauge covariance and Yukawa
restoration are not established. C4 ran independently afterward.

## C4 — The Quotient Admission Test Still Fails For The Raw Probe

Murphy [2005.00059v6](https://arxiv.org/pdf/2005.00059v6), Table 2,
has the three index orders transcribed as `q1`, `q2`, `q3`. The explicit
(+---) contractions and their raw independence are rechecked. The
foundation's paired field/dual dictionary and represented free Higgs
input are now available; they do not make a raw probe admissible.

`C4.witness_zero` places the old explicit divergence at zero in that
actual generated quotient. `raw_probe_rejected` proves there cannot be
an admitted coefficient agreeing with probe 0 on the full source, since
the probe takes that divergence to 1. This rejects the proposed separator,
not the paper's three-operator statement. Invariance of the three
contractions, quotient separators and complete invariant span are still
needed. No fresh basis proof is inferred from the new field dictionary.
The queue proceeded to C5.

## C5 — A New Test Using Both Weyl Equations

Li et al. [2005.00008v3](https://arxiv.org/pdf/2005.00008v3),
Eqs. (4.23)–(4.26), and Murphy Table 5 retain the factor of i,
fermion order and bidirectional Higgs current used in the transcription.
`C5.divergence_identity` checks the finite Pauli signs in the actual mixed
algebra before applying equations. With J defined by that transcription,

\[
\sum_i\partial_iJ_i
 = E_L(0)\chi_0+E_L(1)\chi_1
   +\psi_0E_R(0)+\psi_1E_R(1).
\]

`divergence_eom` proves membership in the two-sided differential EOM
closure. `conserved_products` uses the new generated input to annihilate
p*(div J)*q for arbitrary source elements p,q. `symmetric_current_zero`
then proves every admitted coefficient annihilates the sum of
J_i*partial_i p by actual IBP; no differentiated factor is omitted.
`reorder_value` checks the exterior sign under this same on-shell input.
Generated/direct inverse maps and the original candidate's evaluation
agreement are also retained.

The component route succeeds; no second fallback route is needed for
this identity. This is an algebraic conserved-current test with actual
Lorentz-stable relations, not a proof that the transcribed current is
equivariant or that the bidirectional candidate is nonzero in the quotient.
The physical two-/four-component translation, Higgs EOM, mixed internal
action, invariant support, complete basis and Hermitian real count remain
unproved. Thus the one-coordinate paper target stays partial, and C6 ran.

## C6 — The Finite Substitution Contract Is Retained

Criado–Pérez-Victoria [1811.09413v2](https://arxiv.org/pdf/1811.09413v2),
Eq. (3.2), distinguishes first-order EOM response from higher terms.
For the constructed quartic scalar density and phi -> phi+epsilon*phi^3,
the actual substitution and explicit Euler/divergence formula through
order two are rechecked. `C6.generated_first_zero` tests every coefficient
of the generated input, with the direct/helper inverse laws unchanged.
`second_order_control` retains the exact second term and its raw nonzero
test at g=0. This is not nonzero after EOM/IBP, a literal paper worked
example, or an all-order analytic, amplitude or quantum equivalence result.

## Portfolio Stop

All six cases have terminal outcomes and none prevents the next check.
The added C3/C5 identities and C4 rejection strengthen concrete input
tests. Remaining failures are absent semantic, symmetry or span proofs;
they are not discovered contradictions with the references. The next
foundation projects remain explicit decisions rather than automatic work
inside this recheck. See [verification](verification.md#literature-recheck-gate)
for the current build, strict audits and exact diagnostic commands.
