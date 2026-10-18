# Implementation Plan

## Frozen Statement And Inputs

For a complex coefficient module C define allowed as `∃ c : C, c ≠ 0`
and forbidden as `∀ c : C, c = 0`. For each existing certified linear
equivalence `C ≃ₗ[ℂ] R`, prove both predicates equivalent to their R versions.
For a finite family product, prohibition is equivalent to prohibition of
every factor; allowance is equivalent to allowance of some factor.

The concrete endpoint uses `N : ℕ`, `0 < N`, a residual group realized from
`ZMod N`, and a faithful complex cyclic character with a proved kernel.
Supply five charges for q, u_R, d_R, l, e_R in `ZMod N`. Each flavor carrier
is ℂ (one generation); Higgs has trivial residual action. Charge equality
must follow from the chosen character's kernel, not an unproved exponential
identity. Preserve N=1 and the zero/positive-order distinction.

Prove an iff between:

1. every coefficient in the full signed dimension-six Delta L=+1 sector is
   zero and a nonzero coefficient in the LLHH sector exists;
2. four forbidden-family charge tests together with the allowed LLHH test.

Derive the exact signed expressions from actual representations, including
dual/conjugate adapters. Do not silently use the same sign for a physical
right-handed carrier and its conjugate. If this interpretation differs from
the proposed elementary charge model, document the correction before coding.

## Milestones

1. Inspect `ConstrainedCompleteness`, existing four endpoint equivalences and
   scalar controls. Build a shared transport/prohibition API only for missing
   interfaces; reuse existing nonzero equivalences. Keep optional finite or
   compact hypotheses local to adapters that actually require them.
2. Connect all four endpoints without replacing typed/exchange-constrained
   residual Hom spaces by unrestricted coefficients. Prove family-wise and
   total Delta L one prohibition using `DeltaLOneCoefficientCompleteness`.
3. Inspect Mathlib cyclic-character and root-of-unity APIs. Construct a precise
   character/charge dictionary and prove tensor/dual charge rules. Derive
   each of the four one-generation family tests and the LLHH test from the
   independent coefficient spaces, with converse nonzero witnesses.
4. Combine them into the simultaneous iff. Provide one accepted and one
   rejected finite assignment and the N=1 control. Decide examples only after
   the dictionary is fixed; no phenomenological or anomaly claim attaches.
5. Audit every new public endpoint transitively, build all sources, review
   hypotheses and update dossiers/ledgers. Commit verified milestones.

## Required Interfaces And Boundaries

Known inspected anchors include
`DeltaLOneCoefficientCompleteness.equiv/nonzero_iff` and
`WeinbergScalarFlavor.exists_nonzero_iff_square_trivial`.
`DuueScalarFlavor.exists_nonzero_iff_charge_trivial` is a reuse candidate;
its physical-family adapter and QQQL/QQUE/DUQL character conventions require
further inspection. No missing API is assumed to exist solely from its name.

General generation-dependent charge matrices, arbitrary finite-group character
tables, anomaly cancellation, Yukawa compatibility, quantum exactness,
UV matching, RGE and rates are not required. A faithful character is a
mathematical parametrization, not a derived physical residual symmetry.

Bounded prerequisite lemmas preserving existing decisions may be implemented
and recorded. Stop for a large foundational project, a conflict with existing
decisions, an essential new physical premise, or a counterexample requiring
an endpoint change. Zero/exchange-degenerate general carriers must not be
mistaken for scalar nonzero benchmarks.

## Acceptance And Stop Condition

All four abstract consumers and the specified cyclic simultaneous iff must
be implemented and pass persistent strict transitive audits, focused builds,
full `lake build`, layout, links and diff checks. No custom axioms, `sorry`,
`native_decide`, dependency changes or audit exceptions. Complete documentation
from the final theorem perspective and preserve the stated physical limits.
Master integration requires a separate user request.
