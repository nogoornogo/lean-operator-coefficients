# Derivative-free charge bounds and minimum engineering dimensions

The current finite-domain endpoint is [complete B1 minima on 572 assignments](#complete-b1-minima-on-the-existing-572-assignments):
all 326 allowed rows have exact minima, with 246 all-degree-forbidden rows.
The earlier lower-bound, four-example and partial-interval APIs below are
retained with their original scopes; they are not unresolved current endpoints.

**Every minimum and lower-dimension exclusion on this page is within the
specified derivative-free SM/Higgs coefficient domain.** Covariant derivatives
are absent from both carriers and grading. A derivative insertion changes
Lorentz support, so independent-chirality parity/grade constraints must not be
used to exclude derivative operators. No EOM/IBP-independent EFT minimum,
matching, Wilson-coefficient generation or decay rate is established here.
See [scope and theorem quantifiers](../../RESULTS_AND_SCOPE.md).

[SMChargeDegreeBounds](../../../../../Physics/StandardModel/Operators/Support/Dimension/SMChargeDegreeBounds.lean)
uses the fixed ten signed species dictionary. For every ordered pattern p of
n fermions, with signed charges `(B3,L)=SMQLPatternRequests.blCharge p`,
`charge_degree` proves `|B3|+|L|≤n`. At each species the sum of the two
absolute charges is one; the proof sums these identities and applies the
triangle inequality. No support, neutrality or generation premise is needed.

`selected_degree` specializes to `|B3|=b`. `twiceDimension n h d` is the
natural-number grading `3*n+2*(h+d)`, twice the usual four-dimensional
engineering dimension for fermions and Higgs/dual scalars. `dimension_lower`
gives the corresponding lower bound. This grading does not encode anomalous
dimensions, derivatives, UV matching, amplitudes or rates.

`original_even`, `original_parity` and `residual_linear` connect the actual
original coefficient spaces to even fermion degree, even B3+L, and residual
charge `(B3:k)*q+(L:k)*l`. These reuse the original local coefficient/parity
theorems and scalar q/l separation. They do not weaken statistical support.

`original_lepton_lower` accepts an explicit arithmetic gate excluding all
smaller |L| for the selected |B3|, parity and residual charges. It applies that
gate to every actual allowed original content, with arbitrary Higgs bidegree.
`original_degree_lower` yields `b+lower≤n` and the engineering-dimension
bound. This gate remains an explicit hypothesis of the older generic API.
The default-build row bounds now use the uniform minimum below, without
requiring externally generated arithmetic gates. The retained
[degree-certificate generator](../../../../../tools/structural-support/degree-certificates.py)
is an independent historical cross-check under the opt-in verifier.

## Computed minimum and uniform bounds

[SMFiniteLeptonDegreeBounds](../../../../../Physics/StandardModel/Operators/Support/Dimension/SMFiniteLeptonDegreeBounds.lean)
defines `neutralLeptons` by filtering the proved `leptonRange b` with the
residual equation, and `leptonSizes` by taking absolute values. `minLepton`
returns `Option Nat`: Some m is the least member, and None denotes an empty
set. There is no numerical default for the prohibited case.

For b=3 or 6 and arbitrary nonzero k,q,l, `min_none_forbidden` proves None
iff original-space prohibition, and `min_exists_iff` proves existence of a
numeric minimum iff allowance. `minimum_attained` realizes that minimum in
an actual exact-(B3,L) coefficient space. `minimum_le_eighteen` bounds every
numeric result; thus the finite distribution covers all possible values.

`normalized_content` keeps the actual absolute lepton charge when normalizing
negative B3: it produces a neutral candidate with **the same** |L|. Using
this witness, `original_lepton_lower` bounds every actual allowed content by
the computed minimum, rather than by an unrelated existence witness.
`original_degree_lower` then gives `b+m≤n` and
`3*(b+m)≤twiceDimension n h d`. All Higgs bidegrees are included.

## All 796 allowed-entry applications in the normal build

`b1_row_bounds` and `b2_row_bounds` apply these statements to the Lean-generated
572-row domain. Each allowed row has one computed minimum bounding all its
selected original contents. `minimum_distributions` kernel-proves the complete
minimum-|L| distributions and prohibited-row counts (246 B1, 102 B2).
`allowed_application_count` proves there are 796 allowed row/target pairs;
none of these applications depends on generated certificates or CSV input.
`high_degree_counts` and `high_row_bounds` connect the 278 B1 / 284 B2
groups to their actual degree lower bounds. All are registered library proofs
protected by ordinary `lake build`.

For the 278 B1 rows excluding |L|=1, every allowed content therefore has at
least six fermions and engineering dimension at least nine. For the 284 B2
rows excluding L=0, at least eight fermions and dimension twelve are required.
These are lower bounds. Higgs factors and other support requirements can
make them strict. The four separate exact minima below do not turn these
general row bounds into exact minima. The later B1 strong-bound/matching
result in the final section closes the stated finite B1 domain separately.

The fixed three-generation, derivative-free, neutral-Higgs scalar cyclic q/l
setting is unchanged. The minimum API uses the separately proved finite
attainable-charge theorem; the original count inequality needs no support
premise. `AuditSMChargeDegreeBounds` audits its 13 public declarations, and
`AuditSMFiniteLeptonDegreeBounds` audits all minimum/row-bound/example namespace
declarations transitively against exactly propext, Classical.choice and
Quot.sound. Importing examples cover None, minimum 17 at k=101, the six/eight
fermion lower bounds, and a negative-B3 consumer. Checkpoint evidence belongs to the
[owning topic](../../../../topics/sm-finite-charge-support/README.md).

## Four exact minimum engineering dimensions

[SMMinimumOperatorDimension](../../../../../Physics/StandardModel/Operators/Support/Dimension/SMMinimumOperatorDimension.lean)
defines `IsMinimum q l b M` by actual original-space attainment of doubled
dimension M and a bound for every allowed content with absolute B3=b,
at every Higgs bidegree. It proves uniqueness and prohibition below M.
The grading is the same `3*n+2*(h+d)`; these are global minima within
the fixed derivative-free coefficient input, covering every selected content.

| Cyclic input (k,q,l) | Sector | Exact derivative-free dimension | Attaining content and Higgs |
| --- | --- | ---: | --- |
| (2,0,0) | B1 | 6 | Q³ L; h=d=0 |
| (2,0,0) | B2 | 9 | uR² dR⁴; h=d=0 |
| (3,1,1) | B1 | 9 | uR³ L² eR; h=d=0 |
| (5,1,1) | B1 | 10 | dR³ conjugate(L)³; h=0,d=1 |

Explicit generation occupations and positive **joint** color, weak and both
spin certificates prove each pattern has full statistical support. The
existing `original_ql_iff` supplies actual coefficient allowance. For the
first three cases, the minimum-|L| bound is sharp. For (5,1,1), it gives
only dimension nine. The per-species inequality `abs(Y-B3+6L)≤3` sums to
`abs(Y(p)-B3(p)+6L(p))≤3*n`; charge, parity and hypercharge exclude every
selected content below dimension ten, handling both baryon signs directly.

The fixed three-generation, derivative-free, neutral-residual Higgs scalar
cyclic dictionary is essential. No arbitrary flavor-action, exact-multiplicity,
all-k optimization is claimed by this four-example module. The later 572-row
B1 classification is recorded separately below. These are
allowed coefficients, with no UV-generation or rate consequence. Closed
support certificates use existing decisions checked by the Lean kernel;
no numerical/CSV or new external mathematical premise is introduced.

[Importing consumers](../../../../../Physics/StandardModel/Operators/Support/Dimension/SMMinimumOperatorDimensionExamples.lean)
exercise exact minima, negative B3, the H2 zero-Higgs exclusion and rejection
of false smaller/larger minimum claims. The persistent
[audit](../../../../../Physics/StandardModel/Operators/Support/Dimension/Audit/AuditSMMinimumOperatorDimension.lean)
checks implementation and example declarations transitively against exactly
propext, Classical.choice and Quot.sound. See the
[topic results](../../../../topics/sm-minimum-operator-dimension/results.md)
for verification and scope.

## Complete B1 support strictly below dimension ten

[SMB1BelowTen](../../../../../Physics/StandardModel/Operators/Support/Dimension/SMB1BelowTen.lean)
proves, for arbitrary nonzero k and scalar cyclic q/l actions on the same
fixed SM/Higgs dictionary, actual B1 allowance at `3*n+2*(h+d)<20` iff
`3*q+l=0 ∨ 3*q-l=0 ∨ 3*q+3*l=0` in ZMod k. Its complementary criterion
is universal original-space prohibition below the same strict bound.
Both baryon signs and every content/Higgs degree are covered.

The proved hypercharge envelope excludes normalized L=-3 below ten; degree
and Lorentz parity leave L=1,-1,3. Actual joint certificates realize these
at dimensions six, seven and nine respectively. The necessity proof handles
both signed charge branches without a source-conjugation premise.

[SMB1BelowTenAssignments](../../../../../Physics/StandardModel/Operators/Support/Dimension/SMB1BelowTenAssignments.lean)
reuses the complete unique 572-row domain. Its domain excludes `3*q+l=0`,
so only the other two congruences remain. Kernel counts give 146 below-ten
allowed and 426 below-ten forbidden rows. Of the latter, 180 are allowed
at some higher degree and 246 are forbidden at every degree under the
existing all-degree theorem. Counted classes have original-space semantics.
These are not minimum dimensions for the 572 rows. The (5,1,1) minimum-ten
example tests the strict cutoff and distinction from all-degree prohibition.

New declarations and importing consumers have a persistent strict transitive
audit. No CSV premise, new foundational theory, general solver or physical
scope extension is used. See the [bounded topic](../../../../topics/sm-b1-below-ten/results.md).

## Retained B1 intervals after the full-minimum attempt

[SMB1DimensionBounds](../../../../../Physics/StandardModel/Operators/Support/Dimension/SMB1DimensionBounds.lean)
adds the actual independent-left-chirality and engineering-grade congruence
`(twiceDimension-3*B3+L)%4=0`. The retained interval lower bound uses the
existing absolute-charge bound and complete below-ten exclusion; it does not
assume the stopped proposed complementary-weak envelope.

[SMB1DimensionWitnesses](../../../../../Physics/StandardModel/Operators/Support/Dimension/SMB1DimensionWitnesses.lean)
supplies actual graded witnesses for every one of the 18 normalized B1
charges, reusing old certificates and eight new joint-support templates.
[SMB1MinimumClassification](../../../../../Physics/StandardModel/Operators/Support/Dimension/SMB1MinimumClassification.lean)
proves attained upper grades and universal original-space lower grades for
all 326 allowed rows in the unchanged domain, and kernel-counts 160 exact
minima and 166 nontrivial intervals. Exact rows have minimum dimension nine
or ten. The largest retained row upper dimension is 31, from the diagnostic
inventory; all row intervals have proved actual-coefficient semantics.

At that checkpoint the full-minimum endpoint was not achieved: the attempted stronger weak
connection hit its 10 GiB guard. Its source and diagnostic all-row match
proposal are outside active imports and are not accepted theorems.
No minimum is asserted for unresolved intervals, and the 246 all-degree
forbidden rows keep None. Both baryon signs, all contents and Higgs degrees,
fixed statistics and the neutral-residual scalar-cyclic dictionary remain
essential. The [topic results](../../../../topics/sm-b1-minimum-classification/results.md)
record the exact stop, verification and remaining boundary.

## Complete B1 minima on the existing 572 assignments

The subsequent [connection revision](../../../../topics/sm-b1-weak-connection/results.md)
proves the previously missing weak envelope by three small interfaces:
[abstract count arithmetic](../../../../../Physics/StandardModel/Operators/Support/Dimension/SMB1WeakCountArithmetic.lean),
[actual support extraction](../../../../../Physics/StandardModel/Operators/Support/Dimension/SMB1WeakDimensionBounds.lean)
and [strong signed grade bounds](../../../../../Physics/StandardModel/Operators/Support/Dimension/SMB1StrongDimensionBounds.lean).
The proved `abs(7*L-B3)≤12+twiceDimension` combines with existing capacity,
hypercharge and chirality facts without a new mathematical premise.

[SMB1ExactMinima](../../../../../Physics/StandardModel/Operators/Support/Dimension/SMB1ExactMinima.lean)
proves actual attained global minima for all 326 allowed rows, by matching
the stronger universal lower grades to the unchanged graded witnesses.
All selected contents, both baryon signs and every Higgs degree are covered.
The 246 all-degree-forbidden rows have None, with proved prohibition semantics.
The old interval module is retained as a weaker, historically verified API;
its 166 gaps no longer describe the current finite-domain theorem endpoint.

| Minimum derivative-free engineering dimension | Allowed rows |
| ---: | ---: |
| 7 | 48 |
| 9 | 98 |
| 10 | 62 |
| 14 | 28 |
| 15 | 16 |
| 19 | 16 |
| 20 | 10 |
| 24 | 28 |
| 27 | 10 |
| 31 | 10 |

The distribution and complete lower/upper agreement are kernel theorems on
the inherited uniquely covered 572-row domain, not an imported numeric
table. `row_minimum`, `none_iff_forbidden` and `row_forbidden_below` are the
semantic consumers. Fresh examples close the earlier [6,7] and [21,31]
intervals, exercise negative B3 and keep forbidden rows without a numerical
minimum. A persistent strict transitive audit includes all new namespaces.

This is a finite-domain minimum classification for the fixed derivative-free,
three-generation, neutral-Higgs scalar cyclic dictionary. The generic bound
does not classify minimum dimensions for arbitrary cyclic moduli/actions,
arbitrary flavor representations or B2. No physical generation or rate is
inferred. The old resource stop is preserved; the new proof uses unchanged
limits and dependencies and introduces no axiom or multiplicity premise.

## Arbitrary-modulus interfaces and deferred extension

`SMB1ExactMinima.none_iff_forbidden` and `exact_of_match` are quantified over
any positive modulus. The latter requires both a computed lower grade and a
matching attained upper grade. `row_minimum` supplies that agreement for the
stated 572 assignments; the separate below-ten theorem is already all-k.
The existing `SMB1DimensionWitnesses` supplies witnesses for 18 normalized
lepton charges. An all-k exact-minimum extension would still need agreement
with strong lower grades throughout the required charge range. Neither its
success nor the need for new witness constructions follows from the finite
row theorem. That extension is deferred, not an obligation of this dossier.

## Related dimension-selection literature

[Kobach, *Baryon Number, Lepton Number, and Operator Dimension in the Standard Model*](https://arxiv.org/abs/1604.05726v1)
and [Helset–Kobach, the SMEFT flavor-symmetry study](https://arxiv.org/abs/1909.05853v1)
provide parity and flavor-dependent leading-dimension context. Their arguments
are not external premises of these bounds, and no signed-charge/grade or
flavor-input identification is certified here. The [existing source register](../../../../topics/all-degree-symmetry-protection/references.md#r5--bldimension-selection)
keeps those comparison boundaries explicit. Their broader EFT settings must
not be used to extend this dossier's derivative-free exclusions.
