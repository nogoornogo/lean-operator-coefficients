# Kernel-oriented character evaluation

The refinement preserves the reference multiplicity and actual rank statements.
The [plan](kernel-plan.md) authorizes changes to computation and proof structure,
with no change to the Weyl premise, physical conventions or dependency pins.

## Proved refinements

`SparseWeightPolynomial.mergeFuel` uses an explicit `Nat.rec`; the exterior
degree table uses an explicit `List.rec`. This avoids the earlier accessibility
proofs and automatically generated course-of-values (`brecOn`) histories.
The fuel is the sum of the input lengths, not a theorem hypothesis. Even the
fallback preserves evaluation by concatenation. Evaluation and coefficient
preservation remain uniform, without sortedness or uniqueness assumptions.

`WeightStringExtraction` proves coefficient convolution, commutation of root
differences with extraction, and cancellation of a finite weight string.
`SMHiggsStringExtraction` specializes these identities to the actual Higgs
weights. The weak difference cancels all intermediate Higgs weights, and the
existing A2 formula reduces the color extraction to six terms. Coefficient
lookup skips unmatched terms; its equality to the original coefficient sum is
proved. `multiplicity_eq` is unconditional for arbitrary mixed contents.

For constant-species rows, `SMNeutralSparseRanks.constant_source_row` eliminates
the identity factors from absent species and the degree-zero Higgs factor.
The source is exactly one row of the exterior table. `columnsFast_eq` uses
mathlib's `Nat.choose_eq_fast_choose`: compiled evaluation already uses that
optimization, while kernel reduction needs the equality explicitly.

`SMKernelWeightData.weights_verified` kernel-checks all 180 signed slot weights
against the original field-index construction. Its table equality permits
reuse of these checked inputs. The data generator is not trusted.
`solveDirectWith_data` proves that the resulting constant-row evaluator returns
exactly the original `solve` result, for every row. Consequently the old
conditional kernel/rank consumers apply without a new premise.

The exporter uses this equivalent evaluator and preserves the existing CSV
schema. The separate 107-row output remains distinct from the original
unconditional classifier. Actual kernels/ranks retain the explicit Weyl input.

## Grouped and coefficient-only refinement

`GroupedExteriorPolynomial.rows_evaluation` proves the truncated 1,3,3,1
transition equals three original equal-weight slots. `SMGroupedCharacter`
kernel-checks the grouping of all ten signed slot lists and proves both its
grouped and coefficient-only constant-species evaluators equal the old `solve`.
`BoundedExteriorCoefficient.compute_eq` proves the latter equality from derived
linear support bounds: a pruned coefficient is proved zero, not supplied zero.
There is no new theorem premise or sortedness certificate.

## Arithmetic acceptance

The Q18 numerical source/consumers below are now [archived](archive/q18-numerical/README.md)
after the user selected a [structural support replacement](q18-support-results.md).
The former numbers are historical checkpoint results, not active declarations.


`SMNeutralSparseExamples.q_six` proves multiplicity 261 and rank 5843115 for
Q6,m2,delta=-2. At checkpoint `checkpoint 01`, the later `q_eighteen` proved the original `solve` returned
multiplicity **33573** and rank **63525913527** for Q18,m6,delta=-6.
Its proved column count was **63525947100**. The old `q_eighteen_kernel` and
`q_eighteen_rank` retained exactly the existing explicit Weyl input.

The [Q18 certificate](archive/q18-numerical/Q18.lean.txt)
composes 48 closed coefficient equalities, checked in twelve four-query modules
with chained imports. Every module passed the unchanged 16 GiB / 300 s monitor;
the largest sampled process-group RSS was 14059280 KiB (about 13.4 GiB).
`SMCoefficientAssembly.factor` exposes the coefficient function through a
uniform named interface. Proving the arithmetic assembly for an abstract
function and then supplying checked values avoids elaborator re-expansion of
the expensive closed function. No heartbeat or recursion limit was raised.

The grouped and coefficient-only whole-Q18 reductions still exceeded 16 GiB.
A shared recurrence-state graph reduced memory but exceeded 300 seconds.
Those interruptions are distinct from the accepted coefficient decomposition;
no large unfinished auxiliary table is retained. The additional
whole-Q12,m4,delta=-4 probe was interrupted at 141.5 s and
16781968 KiB sampled process-group RSS. This is the pass's stopping condition.
All-107 arithmetic equality and full q/l searches remain open; closing this
Q18 row is not their completion.

See [verification](kernel-verification.md) for the final Q6/Q18 probes,
arithmetic certificates, bounded interruptions and complete regression checks.
Success of an intermediate prototype is not a certificate for a later variant;
compiled output and independently checked diagnostics remain separate from
closed numerical equalities proved in the kernel.

No full mixed-content or q/l assignment search, Weyl integration proof, other
residual classification, UV realization or rate calculation is introduced.
