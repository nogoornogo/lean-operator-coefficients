# Structural mixed support beyond the symbolic criterion

This continuation from `checkpoint 01` proves new actual exclusions and a complete
mixed-family iff. It does not claim the original full q/l classification is
finished. See the [plan](structural-classification-plan.md),
[remaining interface](structural-classification-boundary.md) and
[verification](structural-classification-verification.md).

Every result below is independent of the external Weyl input and of
numerical character, multiplicity and rank certificates. Algebraic identities
for zero/top exterior powers and symbolic binomial factors are used; no
large concrete basis, character recurrence or rank numeral is expanded.

## Sharp mixed weak capacities and actual exclusions

Write c_s for the actual species count, D_s for its field dimension and
epsilon_s for whether that species is a weak doublet. Define

```text
B(c) = sum_s (if epsilon_s = 0 then 0 else min(c_s, D_s-c_s)).
```

[`ContentTorusBound`](../../../Math/RepresentationTheory/ContentTorusBound.lean)
proves tensor bounds add, and transports them through the complete indexed
exterior-content decomposition, including arbitrary word order.
[`SMMixedWeakCapacity.source_bounded`](../../../Physics/StandardModel/Operators/SMMixedWeakCapacity.lean)
uses each species' proved complementary exterior bound. Weak singlets
contribute zero. Color, flavor and independent spins are retained; no
factorwise-singlet condition is assumed.

`local_high_forbidden` proves every actual local coefficient is zero if
m > B(c). `original_ql_forbidden` proves prohibition at **all Higgs counts**
with `h-d > B(c)` or `h-d < -B(c)`, for every cyclic q/l action. If all weak
doublet species are empty or full, B(c)=0: `saturated_original_ql_forbidden`
decides every case h != d, regardless of the other species' occupation.
This strengthens the previous raw-slot bound, which could count a full
weak-doublet species as contributing D_s rather than zero.

[`SMContentCapacity`](../../../Physics/StandardModel/Operators/SMContentCapacity.lean)
separately handles impossible contents. `source_allowed_iff` proves the actual
fermion statistical source is nonzero exactly when `c_s <= D_s` for every
species. This is a source statement, not permission for invariant
coefficients. If any species overflows, `local_forbidden` and
`original_ql_forbidden` prove every local/all-Higgs coefficient is zero.
The proof keeps binomial factors symbolic and uses the general criterion
that an exterior power is zero above its ambient dimension.

## Completely classified empty/full mixed contents

[`SMSaturatedContentSupport.Saturated`](../../../Physics/StandardModel/Operators/SMSaturatedContentSupport.lean)
means **every** species, not just the doublets, has count zero or D_s. The
source is then a line: every factor is its zero or top exterior power.
`source_dimension` and `model_zero_dimension` express this structural line
identity; they are not a large numerical dimension certificate.

[`ContinuousLineActions`](../../../Math/RepresentationTheory/ContinuousLineActions.lean)
proves any continuous one-dimensional representation of SU2 or SU3 is
trivial. For SU2, pinned proved symmetric-power exhaustion forces degree
zero on each constituent. For SU3, the three actual embedded SU2 planes
generate the group. These are proved identities, without a new highest-weight
or branching premise. `SMCompactLineSupport` applies them to color, weak and
both independent spin factors; only the actual hypercharge character remains.

The already proved hypercharge action and its neutrality then construct an
actual nonzero coefficient. Cyclic q/l separation is retained. The final
`SMSaturatedContentSupport.original_ql_iff` is

```text
Saturated(c) =>
  Allowed(original coefficients at c,h,d)
    iff h=d and hypercharge(c)=0 and residual_charge(q,l,c)=0.
```

`original_ql_forbidden` is the exact negation. This decides zero/nonzero
throughout that mixed subfamily, at every Higgs degree and cyclic order.
No unevaluated Hom, block equivalence, multiplicity, coefficient sum, matrix
kernel or Weyl premise remains in its right-hand side. The field/hypercharge
dictionary and signed convention are unchanged.

## Signed balance and a large actual nonzero family

[`PatternCountSum`](../../../Math/RepresentationTheory/PatternCountSum.lean)
proves word weights equal the sum over their species counts, and matched
opposite species cancel pairwise in an arbitrary additive group. Pairing is
essential: from `charge = -charge` alone one cannot deduce zero in an even
cyclic group. No division by two is used.

[`SMSignedBalance`](../../../Physics/StandardModel/Operators/SMSignedBalance.lean)
specializes this to hypercharge and q/l charge. If positive and negative
counts match in each pair, both charges vanish for every cyclic order.
For **saturated and balanced** contents, `saturated_original_ql_iff` therefore
decides actual support exactly by h=d.

`full_original_ql_iff` covers the fully occupied signed universe: its counts
are the corresponding D_s, so opposite counts match and its actual support
is exactly the Higgs-pair direction, for every q/l assignment. The large
fermion source is handled as a top exterior line, not by expanding its
dimension, basis, invariant multiplicity or rank.

Balance alone for a partially occupied mixed source is **not** asserted
sufficient. For example, the independent chirality constraints remain relevant.

## Exact scope still open

Together with the earlier constant Q/L, conjugation, chirality and four-family
results, the new theorems decide additional mixed regions. General fitting,
partially occupied mixed contents outside those regions still need a proved
positive joint-occurrence rule. The [boundary record](structural-classification-boundary.md)
states that interface and the inspected special-case literature. Another
signed-sum reformulation is not being counted as completion of stage 2.
