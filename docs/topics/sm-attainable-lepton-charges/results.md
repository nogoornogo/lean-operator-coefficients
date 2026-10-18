# Exact finite support result

This records the original stage-2 checkpoint. The subsequent
[Lean-owned enumeration extension](../sm-finite-charge-support/lean-enumeration-plan.md)
replaces the literal row table/renderer described below with candidate
definitions, unique coverage and class-count proofs inside Lean. The earlier
measurements remain evidence for their own checkpoint.

## Resolved endpoint

All capacity/parity candidates are attainable. At positive B3=3 the exact
set is the 18 odd integers from -17 through 17; at B3=6 it is the 19 even
integers from -18 through 18. No candidate remains unknown or requires a
new exclusion theorem. Each has a committed actual joint-source witness,
including exact species counts, (B3,L), Higgs admissibility/hypercharge and
original-space transport. All 14 additional proposed families passed on the
initial balanced occupation/first-component route. No exhaustive content
search or alternate foundational route was needed.

`SMFiniteLeptonSupport.exact_original_iff` gives the exact-selector support
criterion and `original_allowed_iff` covers the absolute-B3 selector for
arbitrary nonzero k,q,l. Necessity uses source capacity, sum-by-species and
Lorentz parity. The negative-B3 case normalizes both charges by sign in the
scalar equation; it does not require new representation duality.
Sufficiency uses the 37 concrete joint witnesses. The
[dossier](../../proof/current/applications/Physics/SM_FINITE_LEPTON_SUPPORT.md)
describes the statements, inputs, proof and applicability.

## Ordinary library protection

The witness and criterion modules are registered in Physics. All 572 retained
verdicts are also committed in `SMFiniteLeptonAssignments`, grouped into
eleven lists to keep the kernel computation depth bounded. `all_domain`,
`row_count` and `all_correct` prove the candidate domain and every proposed
arithmetic verdict. Original-space B1/B2 allowance/prohibition and combined
request iff lemmas apply to any row. This replaces sole reliance on the
uncommitted generated 1716-theorem diagnostic file without deleting it as
an independent cross-check. The normal default-root library build protects
the committed results; no opt-in target is needed to import them.

The retained renderers reproduce both committed modules byte-for-byte and
compare the CSV to the historical output. The opt-in verifier now checks
those identities and the library audit before running the original
certificates and degree lower bounds. Its failure behavior never refreshes
expected data automatically.

The importing examples include the known k=2 mixed request and two k=101
cases outside the old domain: q=28,l=1 allows B1 using L=17; q=10,l=1
forbids B1 even though L=71 solves the unrestricted odd congruence. This
kernel-certified counterexample confirms that the finite capacity restriction
cannot be dropped in the arbitrary-k theorem.

## Verification and failure accounting

All Lean runs use the frozen one-thread, 300-second, 10 GiB sampled group RSS
and 4 GiB reserve conditions, with unchanged pins/options. Successful focused
build of the final witnesses, finite theorem and assignments: 49.4 s,
5853708 KiB sampled group peak. Examples plus persistent namespace-wide audit:
8.0 s, 5206172 KiB, **1154 strict transitive declaration checks**. The audit
includes generated helpers and allows only propext, Classical.choice and
Quot.sound. No custom axiom, sorry or native_decide was introduced.

Failures retained separately:

- First witness module build: 34.1 s, 5712228 KiB. Every joint support check
  passed, but the neutral-charge wrappers had cast/projection type mismatches.
  Normal cast simplification fixed them; the failed file was not accepted.
- Initial capacity module: 5.0 s, 5217464 KiB, with one unused-simp-argument
  warning. Removed the redundant argument before acceptance. The completed
  witness/criterion build then passed: 38.6 s, 5735188 KiB, no warnings/errors.
- Additional |L|≤17 corollary: 6.3 s, 5223076 KiB. Omega needed explicit
  conjunction/absolute-value bounds; exposing those fixed the proof.
- Initial committed assignment consumer: 12.3 s, 5747980 KiB. The closed
  row arithmetic passed; two generic iff lemmas needed numeral-cast
  simplification. The accepted final build above includes the correction.

The final independent cross-check passes with renderer/source and CSV
agreement: old certificates 68.8 s, 7007596 KiB, 3724 strict checks; all 796
degree bounds 84.0 s, 7014352 KiB, 2812 strict checks. These retain the
original generated certificate identity and unchanged verdicts.

The full default-root `lake build GUT` passes all **7342 jobs**, zero
warnings/errors, 9.0 s, 6700660 KiB sampled group peak. Layout passes all
1956 modules; local links, Python syntax/renderer checks and diff checks
pass. The [machine-readable evidence](verification.json) retains measurements
and source hashes. This completes the child proof endpoint. Parent integration
and its verification are recorded separately; no master merge or push occurred.
