# Default-build minimum lepton charge and degree bounds

## Resolved review issue

`SMFiniteLeptonDegreeBounds` now defines the minimum attainable absolute
lepton charge inside the ordinary library. It filters the proved finite
range by the residual equation, takes the finite image under Int.natAbs,
then returns Some of its minimum or None when empty. No CSV or generated
arithmetic gate is a premise. None is not interpreted as a numerical zero.

For b=3 or 6, arbitrary nonzero k,q,l, `min_none_forbidden` proves None iff
original prohibition and `minimum_attained` realizes Some m in an actual
exact-(B3,L) coefficient space. `normalized_content` preserves the actual
absolute lepton charge while normalizing the sign of B3. This supplies the
linked witness needed for `original_lepton_lower`, including negative B3.
`original_degree_lower` then gives n≥b+m and twice engineering dimension
≥3*(b+m) for every selected allowed content and every Higgs bidegree.

The row interfaces quantify over one computed minimum and all contents of
each allowed row. `minimum_distributions` kernel-proves every value from
0 through 18 plus the prohibited counts, and `minimum_le_eighteen` excludes
larger numeric minima. `allowed_application_count` counts all 796 allowed
row/target pairs. The minimum-|L| distributions agree with the historical
CSV selections, but are now ordinary default-build theorems.

`high_degree_counts` proves the 278 B1 and 284 B2 group counts. The generic
`high_row_bounds` gives, respectively, n≥6/D≥9 and n≥8/D≥12. These bounds
are not minimum total dimensions: extra quark pairs, statistics and Higgs
requirements can make them strict. No optimization of engineering dimension,
UV generation, derivative scope or rate is added.

## Consumers, tools and README

Importing examples cover None, a minimum 17 outside the old k≤12 domain,
the B1/B2 high-degree bounds, and a negative-B3 content consumer. All minimum,
row-bound and example declarations have a persistent strict transitive audit;
the older 13-declaration charge-degree audit is unchanged.

The optional Lean CSV exporter now uses the library minimum and chooses a
corresponding signed L, with the original negative-first tie convention. The
output is byte-identical to the historical CSV. The older degree generator
is retained only as an independent historical cross-check. The opt-in runner
builds both active audits before exporting and running those old certificates.

As authorized by the review-response request, the root README's q/l input
row and necessary-condition section now link the exact finite B1/B2 criterion
and Degree interpretation. The text retains the general all-degree theorem
first and limits the new equivalence to the fixed derivative-free
three-generation SM, neutral-residual Higgs and scalar cyclic q/l input.
It does not claim arbitrary cyclic flavor representations or minimum total
operator dimension.

## Verification

All runs retain one Lean thread/process at a time, 300 seconds, 10 GiB
sampled process-group RSS, 4 GiB reserve, unchanged pins/options/allowlists.

| Accepted focused check | Seconds | Sampled group peak KiB |
| --- | ---: | ---: |
| General minimum/attainment/sign/degree proofs | 5.0 | 5208356 |
| Complete row bounds and kernel distribution/count proofs | 22.5 | 6744324 |
| Importing examples and persistent audit | 7.5 | 5204216 |
| Updated optional export and exact CSV comparison | 6.4 | 5101496 |

The minimum audit passes **52 strict transitive checks**, allowing exactly
propext, Classical.choice and Quot.sound. It also imports/replays the base
13-declaration charge audit. The row/count source itself took about 20 s
with cached imports. No failed proof attempt, resource stop, raised limit,
warning or recovery placeholder was needed in this extension.

The final independent regression passes: library audits, updated Lean export
and exact historical CSV agreement; old original-space certificates 66.5 s,
7041596 KiB, 3724 strict checks; old 796 degree certificates 85.2 s,
7013516 KiB, 2812 strict checks. Their generated proof source identities and
verdicts remain unchanged. These are independent historical checks, not
prerequisites of the default-build minimum/row-bound proofs.

The full default-root `lake build GUT` passes **7345 jobs**, zero
warnings/errors, 9.5 s, 6706728 KiB sampled group peak. It includes the new
52-declaration audit, the base 13 and existing finite-support 1199. Layout
passes 1959 modules; local links, diff and Python syntax checks pass. The
[verification record](minimum-lepton-verification.json) retains measurements
and source hashes. Final record-only edits do not alter this Lean baseline
and require no further Lean build.

The review-response endpoint is complete on `proof/sm-finite-charge-support`.
No master merge, push, dependency change or publication occurred. The only
README edits are the user-authorized q/l result/scope and interpretation
links. Minimum total operator dimension remains outside this endpoint.
