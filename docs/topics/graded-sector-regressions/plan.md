# Implementation Plan

## Frozen Claim

For each of two existing sectors, construct a linear equivalence from its
independent invariant coefficient domain to the applicable generic residual
quotient Hom, then prove its comparison to the existing explicit residual
classification. The quotient is constructed by the already proved general
theorem; existing contraction completeness is a comparison theorem, not a
premise of generic completeness.

No numerical statistics, sampled testing, external basis generator or AutoEFT
installation is needed. Fermionic statistics means algebraic signed exchange.

## A. Input And Convention Dictionaries

- Six-quark: locate the actual exterior/model domain in the
  [model-interface topic](../delta-b-two-model-interface/README.md), starting
  from [typed flavors](../../../Physics/StandardModel/Operators/SixQuarkTypedFlavor.lean)
  and [residual Hom](../../../Physics/StandardModel/Operators/SixQuarkFlavorResidualHom.lean).
  Select precisely two up and four down inputs, with the established signed
  field/chirality convention. Record integer baryon charge versus physical
  charge, slot order and local group. Prove action identities and all species
  exchange relations, not just a dimension count.
- LLHH: use [actual SM interface](../../../Physics/StandardModel/Operators/WeinbergSMInterface.lean)
  and [model sector](../../../Physics/StandardModel/Operators/WeinbergModelSector.lean).
  Select two leptons and two identical Higgs inputs. Record the local-group
  projection and its invariant-space correspondence, trivial Higgs residual
  action, and polarization/exterior normalization.
- Reuse [generic separated Hom](../../../Math/RepresentationTheory/TypedMixedSeparatedHom.lean)
  and [graded completeness](../../../Math/RepresentationTheory/GradedMixedCompleteness.lean).
  A fixed-content consumer need not classify unrelated contents at the same degree.

Acceptance: exact types, group actions, support and comparison targets are
written down; mismatches are resolved by proved transports rather than assumed
field identifications. This is the first implementation checkpoint.

## B. Six-Quark Consumer

1. Realize the independently defined sector as the supported generic `(6,0)`
   domain and construct the generic quotient equivalence.
2. Compare with the existing typed-exchange residual Hom through the same
   physical domain; prove extraction and reconstruction diagrams.
3. Prove both inverse laws and transport prohibition/nonzero iff.
4. Transfer the existing one-generation two-coordinate control, making its
   flavor specialization explicit. Do not assume the printed ten-seed span is
   complete at arbitrary down multiplicity.

Acceptance: full flavored-sector comparison, not just the local 25-dimensional
contraction space or a chosen two-dimensional specialization.

## C. LLHH Consumer

1. Realize the independent exterior/symmetric LLHH domain as generic `(2,2)`
   fixed-content input. Prove lepton sign and Higgs symmetry compatibility.
2. Construct the generic quotient equivalence and compare with the existing
   `Hom_R(Sym² F, ℂ)` target using the old actual-field equivalence.
3. Prove extraction/reconstruction diagrams and both inverse laws, keeping
   factors of two and Higgs polarization explicit.
4. Transport prohibition/nonzero iff and the existing one-generation control.

Acceptance: actual LLHH connection, not only a toy mixed-degree regression.
This is deliberately dimension five: its purpose is the multiple-boson-slot
interface. Higgs-dressed higher-dimensional operators are not required here.

## D. Audit And Completed-Result Documentation

- Keep separate six-quark and LLHH source modules and persistent strict audits;
  register new modules in `Physics.lean` (and `Math.lean` only for genuinely
  reusable helpers). Do not import model-specific GUT modules into Physics.
- Run focused builds and strict transitive axiom checks for both consumers,
  then one serialized `lake build`, layout checks, Markdown links and diff checks.
- Update Physics assumptions only at verified milestones. Write completed-result
  proof dossiers for the two connections and record commands/results here.
- Commit coherent checked milestones; do not merge into master without a new
  user instruction. Do not automatically edit root README or literature coverage
  ledgers: these connection proofs do not expand verified paper coverage.

## Stop Condition And Boundaries

Successful completion requires A–D for both sectors. No enumeration of dimensions
eight through eleven, derivatives, field strengths, EOM/IBP, amplitudes, matching,
rates, arbitrary-H decision algorithm, finite all-degree cutoff, multi-Higgs
model classification or unconditional inevitable BNV is included.
Do not change dependency pins or add proof assumptions to force a connection.
An inconsistency of actual inputs or a large missing foundation requires a
documented scope decision before continuing beyond this plan.
