# Exact finite lepton-charge support at B1 and B2

For the fixed ten signed three-generation SM fields, derivative-free
statistics, independent Lorentz actions, neutral-residual Higgs/dual and
scalar cyclic q/l action, the attainable positive-B3 lepton charges are

- B3=3: every odd L with |L|≤17 (18 values).
- B3=6: every even L with |L|≤18 (19 values).

There are no unresolved candidates in these sets. This result concerns
nonzero invariant coefficients, not UV generation, amplitudes or rates.

## Original-space statements

[SMFiniteLeptonSupport](../../../../../Physics/StandardModel/Operators/SMFiniteLeptonSupport.lean)
defines `leptonRange b={L∈[-18,18] | (b+L)%2=0}`. For b=3 or 6,
`exact_original_iff` proves, for arbitrary k≠0,q,l,

```text
OriginalAllowed q l (fun c => c=(b,L))
  ↔ L ∈ leptonRange b ∧ (b:k)*q+(L:k)*l=0.
```

`original_allowed_iff` gives the absolute-B3 form:

```text
OriginalAllowed q l (fun c => c.1.natAbs=b)
  ↔ ∃ L ∈ leptonRange b, (b:k)*q+(L:k)*l=0.
```

`original_forbidden_iff` is its universal non-neutrality complement.
`b1_b2_iff` characterizes the existing B1-forbidden/B2-allowed request.
All contents and Higgs bidegrees are quantified in the unchanged original
coefficient semantics. No multiplicity, Weyl law, numeric rank or supplied
support premise is required.

## Proof and finite witnesses

Necessity uses actual exterior capacity from `SMContentCapacity.Fits`:
the positive-lepton doublet/singlet capacities are 12 and 6, as are the
negative ones. Sum-by-species gives |L|≤18. Existing Lorentz parity gives
even B3+L. At absolute B3=b, `normalize` handles negative B3 by negating both
charges in the residual equation; the candidate range is symmetric. This is
an arithmetic sign argument, without a new conjugate-representation premise.

[SMLeptonChargeWitnesses](../../../../../Physics/StandardModel/Operators/SMLeptonChargeWitnesses.lean)
commits explicit full joint color/weak/left/right witnesses for all 37 values.
Each pattern's species counts and exact charges are kernel-checked, as are a
balanced generation occupation, a joint component and its complete support.
Higgs hypercharge/admissibility and the original-space transport are checked
separately. Per-family `_exact` gives the exact (B3,L) selector. The general
sufficiency proof enumerates only the 18/19 possible integer L values and
applies these witnesses; it does not enumerate all contents or factorize
joint support into unrelated choices.

The 23 earlier families cover B1 through |L|=11 and B2 through |L|=10.
The extra 14 families split a=|L|≥12 into 12 doublets and a-12 singlets.
Additional quark/antiquark pairs supply the required hypercharge and spin
support. The [retained renderer](../../../../../tools/structural-support/finite-charge-witnesses.py)
documents the explicit counts; it is not a theorem premise. Its committed
Lean output is checked by the normal library build.

## Maintained 572-row application

[SMFiniteLeptonAssignments](../../../../../Physics/StandardModel/Operators/SMFiniteLeptonAssignments.lean)
defines candidates and verdicts entirely in Lean. `candidatePairs k` filters
the product of `List.range k` with itself by `(3*q+l)%k≠0`; eleven modulus
batches cover k=2,…,12. `classify` calculates both flags from the proved
finite criterion. There is no supplied 572-row literal or CSV input.

`mem_keys` proves exact domain membership in both directions. `keys_nodup`
and `unique_coverage` prove that each admissible assignment occurs once;
`keys_eq` connects these identities to the computed rows. `row_count`,
`rows_length` and `keys_length` prove the total 572. `partition_counts`
kernel-proves the four class counts 326/144/102/0; the derived B1/B2 totals
are 326 allowed/246 forbidden and 470 allowed/102 forbidden.

`all_correct` follows symbolically from how the flags are calculated, rather
than from a proposed table. `b1_forbidden_iff`, `b1_allowed_iff`, their B2
counterparts and `request_iff` give the original-space consequences for each
row. `class_iff` identifies each counted class with the corresponding original
allowance/prohibition pair; `classCount_rows` identifies the batch sum with
filtering the complete, duplicate-free row list.

Thus ordinary `lake build` protects the finite theorem, all witnesses and all
572 classifications, domain completeness, uniqueness and aggregate counts.
No CSV, Python generator or external count is a proof input. The
[optional exporter](../../../../../tools/structural-support/export-assignments.py)
runs Lean to emit a CSV from these definitions; its CSV and displayed witness
choices are external diagnostics, never premises. The older 1716 generated
theorems remain a separate historical cross-check under the opt-in verifier,
which also compares the optional Lean export to the retained CSV. The earlier
generated literal table and its Python renderer were replaced by the
Lean-owned definitions.

[Examples](../../../../../Physics/StandardModel/Operators/SMFiniteLeptonSupportExamples.lean)
include an imported row request, an allowance at k=101,q=28,l=1 with L=17,
and B1 prohibition at k=101,q=10,l=1 despite an unrestricted odd congruence
solution L=71. This last example demonstrates why an unbounded integer
congruence is insufficient for fixed-generation derivative-free support.

## Boundaries and verification

The theorem does not determine minimum operator dimension. The separate
[degree bounds](SM_CHARGE_DEGREE_BOUNDS.md) remain lower bounds and need not
be saturated by the explicit witnesses. Derivatives/EOM/IBP, other field or
Higgs dictionaries, residual actions beyond scalar cyclic q/l, UV matching,
running and decay physics are outside this result.

`AuditSMFiniteLeptonSupport` strictly audits every declaration in the witness,
finite-support, assignment and example namespaces, allowing only propext,
Classical.choice and Quot.sound. Build/resource evidence and failed attempts
are recorded in the [owning topic](../../../../topics/sm-attainable-lepton-charges/README.md).
