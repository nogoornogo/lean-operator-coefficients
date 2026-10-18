# Frozen initial minimum-dimension plan (stage 01)

## Statement and meaning

Use the existing grading `SMChargeDegreeBounds.twiceDimension n h d =
3*n + 2*(h+d)`. Report physical engineering dimension as half this integer;
do not round, use anomalous dimensions, or confuse n with dimension.

For fixed positive k, q,l in ZMod k and b=3 or 6, define a semantic minimum
certificate at doubled dimension M by these two obligations:

1. There exist n, a pattern p : Fin n → Species, h,d, with
   `abs(B3(p))=b`, actual `SelectionCriteria.Allowed` on
   `SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d`,
   and `twiceDimension n h d=M`.
2. Every such allowed original space, for arbitrary n,p,h,d and either sign
   of B3, satisfies `M ≤ twiceDimension n h d`.

Prove uniqueness of the value from these obligations. A proof-bearing
certificate suffices; no computable global Option-valued optimizer is needed.
If an optional finite search is exposed, distinguish exhaustion of its bounded
domain from all-degree prohibition. Existing `minLepton = none` semantics
already supplies prohibition for the fixed B1/B2 sectors when needed.

All Higgs bidegrees remain quantified in the lower bound, including arbitrary
balanced Higgs dressing. A smaller witness in another signed lepton sector
must not be missed. The target minimizes over the whole absolute-B3 sector,
not over one chosen charge L, content or witness family.

## Frozen initial domain

| Case | k | q | l | Sector | Existing charge lower bound to recheck |
| --- | ---: | ---: | ---: | --- | --- |
| C1 | 2 | 0 | 0 | B1, b=3 | minimum absolute L=1, D≥6 |
| C2 | 2 | 0 | 0 | B2, b=6 | minimum absolute L=0, D≥9 |
| H1 | 3 | 1 | 1 | B1, b=3 | minimum absolute L=3, D≥9 |
| H2 | 5 | 1 | 1 | B1, b=3 | minimum absolute L=3, D≥9 |

These are proposed input-specific lower bounds derived from the existing
charge criterion, not new Lean results or claimed attained dimensions.
C1/C2 are baseline controls; H1/H2 test whether a higher charge lower bound
is sharp, with different residual congruences. If either needs additional
Higgs factors or quark pairs, that cost belongs in the exact dimension.
Do not presume D=9 in H1/H2. Confirm the table with the existing library first.
All four cases are allowed at some degree by the existing finite-charge
criterion; this does not prescribe the minimizing witnesses.

## Existing inputs to reuse

- [SMChargeDegreeBounds](../../../Physics/StandardModel/Operators/SMChargeDegreeBounds.lean):
  grading, charge-degree bound, parity and actual residual charge identity.
- [SMFiniteLeptonDegreeBounds](../../../Physics/StandardModel/Operators/SMFiniteLeptonDegreeBounds.lean):
  `minLepton`, `minimum_attained`, `normalized_content`,
  `original_degree_lower`. Attainment here fixes |L|, not dimension.
- [SMLeptonChargeWitnesses](../../../Physics/StandardModel/Operators/SMLeptonChargeWitnesses.lean):
  actual joint-support witnesses; inspect n,h,d rather than infer optimality.
- [SMJointHiggsSupport](../../../Physics/StandardModel/Operators/SMJointHiggsSupport.lean)
  and [SMJointSupportData](../../../Physics/StandardModel/Operators/SMJointSupportData.lean):
  unchanged full joint support and original-space transport.

Use existing bounded sector certificates where they supply an actual witness
in the same dictionary. An abstract nonzero coefficient in a different domain
does not discharge attainment. Keep color, weak, both spins and statistics
in the same joint branch.

## Two bounded routes

**Route A: sharp existing lower bound.** For each case, calculate its proved
minimum |L|; inspect existing explicit witnesses and try a witness at the
resulting dimension lower bound. Prefer ordinary algebraic family lemmas and
explicit occupation/component/coupling certificates. Prove both original-space
obligations, never merely a numerical answer or a witness upper bound.

**Route B: close the finite gap.** Only when route A is insufficient, take
the smallest upper bound among inspected existing witnesses and proposed
explicit witnesses. Below that bound, n and h+d are bounded by
`3*n+2*(h+d)<M`; enumerate content counts rather than species words, then use
existing charge, hypercharge, capacity, parity and joint-support exclusions.
Prove the bounded-domain reduction and its completeness before relying on
exhaustive rejection. Reuse content permutation transport where necessary.
Do not normalize the sign of B3 in a dimension proof merely from charge-sign
normalization: dimension-preserving actual support transport must be proved,
or handle both signs directly.

Executable metadata may propose witnesses or identify candidates; it is not
a proof oracle. No new computational support-proof engine, multiplicity law,
CSV premise or general solver rewrite is included. If an existing kernel
decision is used for a closed certificate, retain the explicit finite domain
and ordinary semantic bridge, and record its resources. Do not add a new
reflection framework or `native_decide` proof path.

One pass through A and, if needed, B for the four cases. Before launching B,
record the concrete witness upper bound, remaining lower dimensions and finite
candidate count in this topic. Do not expand the domain to make a failed route
look successful. A new theorem-level prerequisite outside existing support/
finite-content interfaces triggers a scope decision rather than a foundational
project. General all-k formulas and 572-row optimization require a later plan.

## Outputs and verification

Proposed source: `Physics/StandardModel/Operators/SMMinimumOperatorDimension.lean`,
with an importing examples module and a persistent Physics audit. Final names
may follow source discovery; no new Math foundation is planned. Register new
modules/audits in Physics. Add an application dossier or extend the existing
degree dossier, and update the actual assumptions ledger only at proved
milestones. Preserve the root README unless separately directed.

Each case reports: exact M and D with attainment and universal lower bound,
or a proved interval with the unresolved dimensions and reason. The desired
endpoint is four exact minima; a resource/foundation stop is a bounded partial
result, not success on that endpoint. Review whether sharpness generalizes,
but record that as a proposal, not additional implementation.

Implementation uses the previous bounded-check profile as the proposed cap:
one Lean process at a time, one thread, 300 seconds per check, 10 GiB sampled
process-group RSS and 4 GiB host reserve. Do not raise caps, pins, options or
audit allowlists. Stop and retain evidence on a limit breach.

Run focused Lean builds and fresh importing applications, strict transitive
axiom audits, then one serialized full default-root `lake build GUT`.
Run layout, local-link and diff checks; record commands, warnings, failures,
measurements and agreement of theorem statements/dossier/assumptions. Reuse
existing regression checks when their covered definitions change. No need to
regenerate unrelated assignment tables. Commit coherent verified milestones;
no merge into master, push or publication is authorized.

## Planning checkpoint

Only this plan, its topic record and the topic navigation entry are changed.
No theorem has been implemented or newly verified. Planning checks are
`node tools/docs/check-links.mjs` and `git diff --check`; no Lean build is rerun.
The untracked user file `docs.zip` is preserved and excluded from the commit.
