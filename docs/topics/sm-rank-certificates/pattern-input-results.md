# Fixed-input q/l pattern requests

For the existing three-generation signed SM fields, one residual-neutral
Higgs/dual and scalar cyclic q/l action, the new request facade supplies the
field/content/test dictionaries and separates requirements from their proof.
The forbidden/allowed sets remain the existing `MixedSelectionRequests.Request`
data. No general or model-specific checked API is removed.

## Reader input

Use [SMQLPatternRequests](../../../Physics/StandardModel/Operators/SMQLPatternRequests.lean)
for this fixed input class. Supply the positive cyclic order k and q,l in
ZMod k, then choose forbidden and allowed targets independently. B1 means
absolute 3B=3, B2 absolute 3B=6 and L2 absolute L=2, exactly as in the existing
catalogue. The neutral Higgs has no B/L charge.

The specific request is already defined as

```lean
def b1ForbiddenB2Allowed : SMQLPatternRequests.Request :=
  ⟨{.bOne}, {.bTwo}⟩
```

The library's `SMQLPatternRequests.b1ForbiddenB2Allowed` supplies this data.
`b1_b2_original_iff` proves satisfaction means all original B1 content/Higgs
coefficient spaces are forbidden and some original B2 content/Higgs coefficient
space is allowed. This semantic bridge does not require Weyl extraction.
The arbitrary predicate versions also support other B/L targets without
turning every target combination into a new model theorem.

To discharge the request through the extraction route, supply the explicit
Weyl reduction law for the valid finite table entries (`ReductionInput`).
`b1_b2_iff` gives exactly these proof obligations:

1. For every selected B1 entry, total q/l charge is nonzero **or** the extracted
   local multiplicity is not positive.
2. Exhibit one selected B2 entry with zero total q/l charge and positive
   extracted multiplicity.

The actual proposition uses `not EntryAllowed` for exclusion, with
`EntryAllowed = charge-zero and positive-multiplicity`. The listed disjunction
is its classical logical expansion. The witness belongs to a checked entry
with the actual species content and bounded Higgs representative; no separate
assumed nontrivial source, contraction completeness or rank value is supplied.
`allow_of_entry` turns such an entry into an actual allowed target family.
`forbid_of_charge` provides the direct exclusion route without any external
Weyl parameter when every selected entry is charged.

This request definition does not assert that a particular choice of q,l
satisfies it. The noncomputable spectral polynomial is unchanged. The facade
reduces and organizes proof inputs; it neither evaluates all ranks nor searches
for a protecting model.

## Actual coefficient and all-degree connection

`Entries select` is the finite subset of the proved global table whose
representative counts s,t satisfy s+t<=N_p and whose actual content B/L charge
satisfies select. Pattern words have length at most 180; s,t belong to Fin181.
The table is redundant and potentially enormous, and is never enumerated.
`Coefficients` is a product of the actual full-group `TableTest` spaces for
these selected entries, not a collection of Boolean support assumptions.

`entry_original` proves an allowed constituent gives an actual allowed
original coefficient at representative counts s,t. It uses the bounded
constituent inclusion; it does not claim the whole original representative
space equals that single constituent. Conversely, the original all-degree
support theorem extracts some surviving finite test and handles degrees above
180 by vanishing. Together they prove `allowed_iff_original` and
`forbidden_iff_original`, including empty/zero selections and statistics-killed
contents.

`selector_matches_existing` proves the B/L selector agrees with the earlier
`ComposableBLSupport.specification`, using the same species signs and charge
normalization. The facade does not assert a new linear equivalence with every
earlier model-specific domain; the all-degree semantic bridge is to the actual
fixed-input `OriginalSpace` family.

`satisfies_iff` transforms any existing request into finite universal exclusions
and an independent existential witness for each allowed target.
`original_request_iff` connects the same request to the original all-degree
spaces without literature inputs. Request combination/conflict/empty rules
remain those of the existing generic interface. Allowance of a union does
not replace a witness for each requested target.

## Appropriate route and boundaries

Prefer this facade for compatible fixed three-generation, residual-neutral
single-Higgs, scalar q/l requests. Generic residual actions, different flavor
carriers, charged or residually active Higgs and prescribed LFV selector outputs
continue to use the original admitted-domain interfaces. In particular the
BGW charged-Higgs LLHH and DGT UV/IR selector examples are not rewritten as
instances of the neutral-Higgs q/l model.

The exact request semantics and charge-only exclusion are unconditional Lean
results. Multiplicity-based conditions retain the explicit Weyl reduction
input. Spectral multiplicities are noncomputable; this is not an executable
request checker, numerical classification or a 572-assignment recount.
No UV realization, coefficient generation or rates follow from allowance.

The later [computable character consumer](../sm-computable-characters/results.md)
provides `SMComputableQLSupport.test` and a request iff using its executable
per-entry Boolean. It proves the actual character presentation and preserves
this Weyl-input boundary. The reference term lists are not an efficient
all-content request search; the original spectral facade above remains valid.

Persistent audit: `AuditSMQLPatternRequests`.
See [plan](pattern-input-plan.md) and [verification](verification.md).

## Direct structural support inputs for constant Q/L contents

The [non-numerical support consumers](../sm-computable-characters/non-numerical-support-results.md)
now eliminate local multiplicity tests for every constant positive L content
and constant positive Q content through degree 18 on the original Higgs
spaces. `SMLowerHiggsSupport.lepton_ql_all_iff` and `quark_ql_lower_iff` reduce
those entries to explicit parity, capacity and hypercharge/residual charge
conditions, without a Weyl input. They also prove the forbidden iff. These
can discharge the corresponding original-space request obligations directly.
Mixed-content exclusions needed for a full Delta-B=1 prohibition request,
upper-half Q, signed conjugates and the full assignment search remain separate;
the new consumers do not certify that whole request by themselves.

The [signed/mixed continuation](../sm-computable-characters/signed-mixed-results.md)
now supplies original-field predicates for all constant Q/L degrees of both
signs and individual admissible constituent predicates through
`SMAdmissibleConstantSupport`. `SMMixedFamilySupport.original_ql_iff` and its
conjugate companion connect the four existing mixed families to the same
original-field interface. `SMChiralitySupport.original_forbidden` discharges
any content with odd left or right slot count; `SMMixedConjugation.original_ql_iff`
transports arbitrary signed opposites. No new Weyl input or numerical equality
is needed. These supply the corresponding pattern obligations; unresolved
even/even mixed contents and the full assignment search remain separate.
