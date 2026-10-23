# C5 Coefficient Completeness

[WeylHiggsCompleteness.equivalence](../../../Physics/FieldTheory/Jets/WeylHiggsCompleteness.lean)
proves that candidate evaluation is a complex linear equivalence from
every admitted invariant coefficient on the entire mixed grade (2,4,1)
to ℂ. The space has complex dimension one. An explicit normalized
coefficient, reconstruction, both inverse laws, extraction and agreement
with the generated Euler presentation are proved. No rank, moment,
source-spanning or invariant-extension premise is left to the caller.

## Exact input

[WeylHiggsInput](../../../Physics/FieldTheory/Jets/WeylHiggsInput.lean)
fixes one charged-lepton Weyl/conjugate pair and Higgs/dual components in
the exterior/polynomial jet algebra. The actual global covering-SM group
times SL(2,C) acts with integer hypercharges (+6,-6) and (+3,-3), color
trivially, and ordinary symmetric derivatives in signature (+---).
Formal conjugate components remain independent complex generators.

Both free massless Weyl families and the four free Higgs equations generate
the full unbounded two-sided differential closure. IBP adds the linear
divergence range, without closing IBP under multiplication. Selection takes
the preimage of all these relations on the entire grade, including every
chirality, component and derivative allocation. Hypercharge balance is a
derived constraint, not a source restriction. The
[generated/component equality](../../../Physics/FieldTheory/Jets/WeylHiggsRelations.lean)
compares the union of the computed Weyl and Higgs Euler families through
their complete relations and both coefficient transports.

The representative is i times the ordered lepton Pauli current contracted
with the Higgs bidirectional current, times the Higgs norm. The
[vector/dual dictionary](../../../Physics/FieldTheory/Jets/WeylHiggsCurrent.lean)
proves its arbitrary-group invariance. The
[Minkowski block dictionary](../../../Physics/FieldTheory/Spinor/MinkowskiWeylCurrent.lean)
fixes the four-component translation, (+---) Clifford law and Grassmann
minus for the raised reversed current.

## Whole-source upper and full-relation lower

[First-jet words](../../../Math/Algebra/MixedFirstJetWords.lean) and their
[actual tensor connection](../../../Physics/FieldTheory/Jets/WeylHiggsFirstSource.lean)
span the entire selected source. Actual Lorentz group elements constrain
each spinor/dual-direction tensor; both Weyl equations remove the odd
derivative allocations. Actual internal group elements reduce the remaining
marked Higgs quartics to two coordinates A,B. Linear IBP gives A+B=0,
and candidate evaluation is 24i(A−B). The
[whole-grade upper theorem](../../../Physics/FieldTheory/Jets/WeylHiggsUpper.lean)
therefore proves injectivity. Its ordinary relation-annihilating extension
is invariant only where derived, on the selected grade.

The lower construction uses
[Grassmann-valued four-wave evaluations](../../../Math/Algebra/MixedFourWaveEvaluation.lean).
Kernel stability and a complete
[two-sided normal form](../../../Math/Algebra/TwoSidedDifferentialNormalForm.lean)
prove annihilation of every equation product/descendant; conserving
momenta annihilate all linear IBP. No degree cutoff is substituted for
the full relations. Four null momenta and exact inverse-Pauli moments give
a [wave sum](../../../Physics/FieldTheory/Jets/WeylHiggsWaveSum.lean)
with candidate value 384i.

Its first-word moments equal invariant spinor/vector contractions and a
marked paired Higgs tensor. This proves
[arbitrary actual-group invariance](../../../Physics/FieldTheory/Jets/WeylHiggsWaveInvariant.lean)
on the whole grade, rather than inferring it from density invariance.
Division by 384i gives the admitted coefficient with value one. This also
proves nonzero support in the full quotient. The upper and lower results
assemble the equivalence and dimension theorem.

The independent 56-variable rank-55 model remains a diagnostic. No
identification of all its rows with a full relation-preimage basis is
claimed or needed: the proved route uses whole-source tensors for the upper
bound and full unbounded relations for the lower witness.

## Verification and limits

[Native literature consumers](../../../Physics/FieldTheory/Jets/WeylHiggsCompleteLiterature.lean)
give Li and Murphy extraction, normalized value one and both inverse laws.
DHM supplies the independent block/sign check. Doubling the Li factor or
omitting the Grassmann reversal minus is detected by the admitted coefficient.
The [ordered comparison](literature-validation.md) records all three sources
and the continue-after-discrepancy diagnostic. Strict audits, focused and
full builds and repository checks are recorded in [verification](verification.md).

The [earlier partial checkpoint](input-checkpoint.md) and intermediate
[foundation](foundation-progress.md), [Lorentz](reduction-progress.md) and
[upper](upper-progress.md) records retain the proof progression. The
[resumed contract](completeness-plan.md) is fulfilled. The user subsequently
closed this scope and authorized master integration. The
[integration record](master-integration.md) documents the successful merge,
merged-state verification and safe local branch cleanup.

This certifies the fixed free, ordinary-derivative, one-flavor sector.
It does not certify full SMEFT, interacting gauge/Yukawa EOM, arbitrary
flavors, physical conjugation or a Hermitian real dimension, analytic
actions, amplitudes, matching, running or rates. Published inputs and
dependency pins are unchanged.
