# Computable weights and actual conditional support

This records the reference checkpoint `checkpoint 01`. The later
[sparse refinement](sparse-results.md) closes its all-107 execution boundary;
the original binomial-length analysis below still describes the reference.

The reference executable now constructs finite integer terms for every signed
species content, including arbitrary mixtures, and every Higgs constituent.
Its semantic connection is a uniform proof, not a table of asserted ranks.

## Actual presentation

`SMComputableSlotWeights.field_eigen` proves a simultaneous eigenbasis for the
actual combined compact field action at the six-coordinate torus. Color
fundamentals have weights (1,0), (0,1), (-1,-1); dual gauge carriers negate
their weights. Weak and active left/right spin slots have weights ±1. Signed
species exchange the active spin factor. Hypercharges and the three flavor
copies retain the existing dictionary. Explicit finite index equivalences
make these weights executable; no eigenspace or basis is selected at runtime.

`ComputableWeightPolynomial.exterior_evaluate` and `exterior_ofFn_evaluate`
prove the include/exclude reference recurrence equals the exterior generating
function. `exterior_above` handles capacity and `exterior_length` proves the
reference list has binomial length. Products and shifts have proved evaluation
identities; a proof-only finite-support presentation has exactly the same
coefficients. Mathlib's fixed `Finsupp` API remains noncomputable, so executable
lists and their semantic `Finsupp` view are distinct interfaces.

`SMComputableCharacter.source_evaluation` instantiates the existing finite-tree
decomposition at the actual independent-spin compact action, for arbitrary
ordered words. Exterior characters multiply according to species counts.
The Higgs constituent contributes weak weights `2*j-m` and hypercharge
`3*delta`. `terms_evaluation` transports the inverse character to the existing
analytic compact model. `SMComputableSupport.presents` is unconditional.
No equality with the earlier noncomputable spectral polynomial is needed.

## Executable extraction and consumers

`SMComputableCharacter.multiplicity c m delta` executes positive-root
constant-term extraction on the finite integer terms. Under the unchanged
`SMCompactMultiplicity.Input`, `SMComputableSupport` proves actual kernel
finrank, rank subtraction, nonnegativity and local support iff positivity.
The compact comparison, continuity, statistical source and presentation are
proved; only the existing Weyl reduction law is an external theorem parameter.

`SMComputableQLSupport.test q l p m delta` is an executable Boolean for charge
neutrality and positive extracted multiplicity. `test_allowed_iff` connects it
to actual full q/l coefficients under the same reduction input.
`original_allowed_iff` and `original_forbidden_iff` handle arbitrary original
Higgs counts through the existing bounded constituents. `satisfies_iff` reuses
the actual request domains and supplies an executable test per finite entry;
forbidden targets exclude every selected entry and each allowed target has
its own witness. It does not enumerate the whole request domain efficiently.

## Bounded arithmetic and resource boundary

`SMComputableCharacterExamples` stores kernel-checked integer/Boolean controls:
empty content, LLHH/conjugate LLHH (6), charged/odd/top/above-capacity cases,
a mixed eR/conjugate-eR spin exclusion, and neutral/charged residual tests.
The L4,m4,delta4 control extracts 6. Its conditional actual kernel/rank consumer
has 2475 columns and rank 2469; it is the row still marked `unclassified` in
the existing unconditional CSV. No CSV status is upgraded through an external
Weyl premise, and no Python value is imported as a Lean premise.

The unmerged reference terms have length `choose(dimension,n)` before Higgs
convolution: Q middle degree has 9,075,135,300 terms and Q24 has 1,251,677,700.
Materializing those terms exceeds the bounded lightweight calculation scope.
The uniform presentation/support endpoint is reached; all-107 evaluation is
deferred at this recorded computational boundary. Sparse weight aggregation
and a memoized degree-table refinement need their own correctness proofs
before those evaluations. No billion-term attempt or resource-limit increase
was made. The 572 assignments are not reclassified; all-target content search
also needs an independently assessed compression/search strategy.

Other residual classes, charged Higgs, derivatives/EOM/IBP, multiple Higgs
copies, UV realization and rates remain outside this result. The Weyl law
itself and its compact Lie geometric prerequisites remain documented inputs.
See [verification](verification.md) for build/audit and diagnostic evidence.
