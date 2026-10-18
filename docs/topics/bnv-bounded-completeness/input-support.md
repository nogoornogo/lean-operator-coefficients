# Independent Input And Arithmetic Support Checkpoint

## Established

- [BnvMixedInput](../../../Physics/StandardModel/Operators/BnvMixedInput.lean)
  defines the full signed fermion exterior carrier tensor the symmetric
  H/conjugate-H carrier, with gauge/Weyl and supplied residual invariance.
  No allowed-family list or lepton charge is built into its BNV subspace.
  The degree window uses `Fin 8 × Fin 12`, containing every pair satisfying
  `3 n + 2 m ≤ 22`; out-of-bound components are zero.
- [MixedWeightSupport](../../../Math/RepresentationTheory/MixedWeightSupport.lean)
  proves determination by pure inputs, scalar separation and full-circle
  weight neutrality. Boson weights and actions are retained.
  `BnvMixedInput.hypercharge_of_nonzero` applies that theorem to the actual
  signed fermion and Higgs gauge actions for arbitrary slot counts.
- [BnvBoundedSpecies](../../../Physics/StandardModel/Operators/BnvBoundedSpecies.lean)
  classifies the arithmetic necessary conditions through seven as four
  dimension-six and four dimension-seven types and their conjugates.
  It proves arithmetic exclusion below six and the four/six fermion classes
  and baryon changes of magnitude one/two through eleven.
  Positive-baryon candidates have `(dimension, Delta L) = (6, +1)` or
  `(7, -1)`; this grading is derived, not selected in the input.

The arithmetic assumptions are hypercharge neutrality, color triality,
nonzero baryon charge, even fermion count and even left-Weyl count.
Hypercharge neutrality, color triality and even total fermion count are now
derived from the actual mixed action for arbitrary slot counts. For four
fermions, the nonunitary Weyl test also derives even left-Weyl count, and
`BnvMixedWeylSupport.seven_support_of_nonzero` derives the eight-family
support directly from a nonzero invariant value. Pure typed values determine
the whole mixed coefficient (`MixedSpeciesExt.ext`), so
`BnvMixedInput.bounded_eq_zero_below_six` proves that the entire bounded BNV
coefficient space below dimension six is zero. Their classification
does not prove local invariants exist, span, or have the required statistics.
Neither the seven-dimensional nor eleven-dimensional acceptance gate passes.

Both scalar flavor carriers are supplied algebraic representations. The
physical conjugate identification is not inferred from those independent
inputs; actual-field transport remains an explicit future obligation.

## Verification

- Focused `lake build Physics.StandardModel.Operators.Audit.AuditBnvBoundedSupport`:
  passes; 40 strict transitive checks permit only `propext`, `Classical.choice`,
  `Quot.sound`, and reject model-layer imports.
- `lake build`: passes, 6,455 jobs.
- `node tools/layout/check-layout.mjs`: passes, 1,128 modules.
- `python3 tools/bnv-support-check.py`: exact arithmetic cross-check passes;
  173 positive-baryon necessary-condition types through eleven. This script
  neither establishes local invariants nor replaces any Lean proof.

The initial unrestricted arithmetic tactic search was replaced by smaller
fermion-count, antiquark, scalar-count and lepton-count cases. The final
classification is kernel-checked, not an external enumeration assumption.
