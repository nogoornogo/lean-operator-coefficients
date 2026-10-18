# Delta L one dimension six coefficient completeness

- ID: `delta-l-one-completeness`
- Status: completed
- Checkpoint detail: completed; integrated into master
- Result type: total bounded coefficient completeness with checked inverse maps
- Working branch: `proof/delta-l-one-completeness`
- Integration target: `master`
- Integration evidence: topic endpoint `checkpoint 01`; user-authorized no-ff master merge `checkpoint 02`; post-merge verification passed

## Accepted endpoint and scope

The accepted endpoint is completeness of the derivative-free,
dimension-six four-fermion sector with lepton degree `+1`, using only the
Standard Model fermion species and their conjugates. It is not a classification
of Delta L one at arbitrary dimension. This restriction is an explicit planning
choice, accepted before implementation.

Use the existing SM covering-product gauge group and Weyl actions, an explicitly
supplied residual group `R`, and complex multiplicity representations for
`q`, `u_R`, `d_R`, `l`, `e_R`. No right-handed neutrino or other extra species
is included. Keep conjugate and physical-right-handed conventions distinct.
Do not identify a conjugate representation with a complex linear dual without
an appropriate proved adapter. No topology, compactness or self-duality is
assumed by coefficient completeness. Omit finite-dimensionality except where
an explicit dual-to-Hom conversion needs it; the existing qque conversion
requires finite-dimensional up-conjugate and electron-conjugate multiplicities.

Define the input coefficient sector independently as the invariant alternating
four-field coefficients of the specified lepton degree on the full supplied
field sum. Do not define it as the image of contractions or as the sum of four
preselected operator families. Prove the supported species patterns first,
then prove their individual coefficient classifications and the total split.

Expected families in physical-field notation are `duql`, `qque`, `qqql`,
and `duue`. These are the four SM dimension-six baryon-violating families in
[Alonso et al., Eq. (1)](https://arxiv.org/html/1405.0486v2#S1).
The source is a convention and comparison reference, not an assumed Lean
completeness theorem. The Delta L one sector's reduction to these families,
including exclusion of conjugate mixtures, is now proved for the canonical
signed gauge/Weyl fields with arbitrary supplied residual multiplicities.

The proved final classification has the form

```text
IndependentDeltaLOneSector ≃ₗ[ℂ]
  ResidualDuql × ResidualQque × ResidualQqql × ResidualDuue.
```

Each right-hand factor is an explicit residual intertwiner space, with the
proved finite permutation constraints for qque and qqql. There is no unresolved
SM/Lorentz invariance condition on the right. Extraction, reconstruction, both
inverse identities, and the nonzero existence iff are proved; the factors are
not unclassified physical Hom spaces.

## Deliverables and order

1. **Scope and species support.** Freeze signed field conventions, the input
   representation, degree predicate and invariance. Prove necessary color,
   hypercharge and Lorentz constraints on all four-slot signed species patterns.
   Use a small finite enumeration only after proving those necessary conditions.
   Derive the four supported families and baryon degree `+1` in this convention;
   do not silently restrict to baryon degree `+1` at the outset.
2. **Reuse qque and pilot duql.** Transport the existing qque equivalence with
   its actual hypotheses and normalization. For duql, distinguish the existing
   charge/contraction signature from a coefficient completeness theorem. Prove
   local invariant-factor exhaustiveness, residual extraction, construction and
   inverse identities. This is the first new complete sector milestone.
3. **Classify duue.** Treat the repeated up species and four right Weyl slots.
   Prove all needed epsilon/Schouten relations and simultaneous flavor exchange
   laws. Do not assume one local contraction or symmetric up flavors in advance.
4. **Classify qqql.** Treat three repeated quark slots, four weak doublets and
   four left Weyl slots. Prove the coupled color/weak/spin/flavor permutation
   relations. Specify the residual space from these relations, then prove
   exterior descent and the inverse. This is the main feasibility risk.
5. **Assemble total completeness.** Prove species-degree splitting of the
   independently defined full sector and combine all four equivalences. Prove
   existence of a nonzero total coefficient iff one residual factor is nonzero.
   Connect negative lepton degree by a properly typed conjugation statement;
   complex conjugation is not a complex-linear equivalence.
6. **Actual fields and regression controls.** Transport through supplied
   equivariant field identifications. Check zero species, trivial residual
   one-generation specializations, normalization and nontrivial residual
   charges. Prove each dimension claimed; do not conflate four operator
   families with four coefficients at arbitrary multiplicity. Existing input
   APIs stay unchanged; cross-topic API unification remains deferred.
7. **Audit and integration review.** Register modules and strict transitive
   axiom audits, run focused and full builds, layout/link and diff checks.
   Review necessary versus sufficient conditions and all input obligations.
   Commit verified milestones. Merge requires separate authorization.

## Feasibility and stop conditions

Start with one bounded feasibility pass over two routes: local invariant-factor
classification with permutation-module descent; or general multilinear expansion
with a small exact relation certificate and the same descent. No large generated
coordinate-elimination proof lists. Keep certificate computation separate from
the mathematical reduction and verify certificates in Lean.

Do not predict the exact qqql/duue residual functor before verifying the slot
relations. An explicit kernel of finite equivariant permutation relations is an
acceptable endpoint; a named Schur-functor decomposition is optional, not a
prerequisite. Stop for scope approval if neither route fits existing tensor and
exterior foundations, if additional physical assumptions are needed, or if the
proposed four-family support statement fails. A completed duql pilot alone
must not be reported as full Delta L one completeness.

The general B/L parity selection rule is not a prerequisite. Exclude arbitrary
dimensions, added sterile neutrinos, Higgs/derivative/field-strength operator
classification, EOM/IBP quotient infrastructure, UV matching, RGE, matrix
elements and decay rates. The theorem cannot imply a nonzero generated Wilson
coefficient or proton-decay amplitude. No dependency-pin changes are planned.

## Current evidence and next action

- [Qque completeness](../qque-coefficient-completeness/results.md) supplies a
  proved independent-sector inverse and actual-field transport. Reuse
  [QqueCoefficientCompleteness](../../../Physics/StandardModel/Operators/QqueCoefficientCompleteness.lean).
- [StandardModelLocalOperator](../../../Physics/StandardModel/Operators/StandardModelLocalOperator.lean)
  supplies physical-field charges and qque/duql dimension-six signatures.
  Its two-element `StandardOperatorClass` is not an exhaustive four-family theorem.
- [Weinberg results](../delta-l-two-weinberg/results.md) supply normalized
  two-left-spinor and residual extraction examples; two-spinor uniqueness does
  not establish the four-same-chirality spinor classification.
- [Six-quark residual Hom](../delta-b-two-model-interface/flavor-hom.md)
  supplies a design precedent for explicit flavor permutation constraints.

The first implementation checkpoint establishes the arithmetic four-family
reduction and the independent duql exterior-sector equivalence with residual
Hom. See [results and verification](results.md) for exact interfaces and limits.
The arithmetic conditions are now derived from the full signed-field action;
the input imposes lepton degree, not a four-family support condition.

The two-coordinate classifications of four SU(2) doublets and four same-chirality
Weyl spinors are also proved, before repeated-species constraints.

The independent duue exterior sector is now classified by one unrestricted
residual Hom, after solving the repeated-up exchange equations. Both inverse
identities, actual-field transport, the scalar residual-charge criterion and
the one-generation dimension-one specialization are proved.

For qqql, the physical degree-(3,1) exterior sector is classified by the explicit
four-coordinate residual exchange kernel. Hypercharge cancellation, all local
gauge/Weyl factors, both inverse identities and actual-field transport are proved.
The neutral one-generation specialization has dimension one.

Signed-field support and the shared physical qque classification are proved.
See [signed-field results](signed-fields.md) for the exact input and conjugation
obligations. The full-sector species projectors are connected to all four individual
classifications by normalized ordered-pattern assembly. The
[total residual equivalence](../../../Physics/StandardModel/Operators/DeltaLOneCoefficientCompleteness.lean)
has both inverses and the nonzero iff. Supplied actual-field identifications
transport the independent input sector to this equivalence. Regression controls
prove neutral one-generation dimension four, disappearance of families with
missing species, and vanishing when all four scalar product characters are
nontrivial. Negative degree is classified semilinearly when the explicit
species-reversing conjugation inputs are supplied. See [results](results.md).
No cross-topic input-interface refactor was performed. The topic branch is
retained; no remote push was made.
