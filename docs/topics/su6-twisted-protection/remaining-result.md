# Pointwise Inner And Gauge-Equivalent Patterns

## Verified Statements

[PointwiseGaugeRemoval](../../../Math/RepresentationTheory/PointwiseGaugeRemoval.lean)
works for an arbitrary field, local group representation and supplied genuine
residual action covariant under a supplied automorphism action. For any function
`s : H → G`, define `C(h) = a(s(h)⁻¹) U(h)`.

- Physical and removed maps induce the same action on local coinvariants.
- `C(h) C(l)` and `C(hl)` agree after projection, without a homomorphic lift.
- Locally invariant functionals give the same values on physical and removed maps.
- If `s(h)` implements the inner automorphism, each `C(h)` commutes with the
  local representation. No field-level group law for `C` is asserted.
- For two supplied genuine covariant actions `U` and `B`, the checked equality
  `U(h)v = a(s(h)) B(h)v` implies equality of their coinvariant representations.
  Their invariant coefficient spaces are linearly equivalent; both zero and
  nonzero coefficient statements transfer.

The comparison is valid without an inversion or innerness hypothesis. It
therefore gives a test applicable to non-reversing candidates too. It does not
supply the reference action or prove the comparison certificate for a candidate.

[GaugeEquivalentCandidate](../../../GUT/SU6/SelectionRules/Models/GaugeEquivalentCandidate.lean)
specializes these tests to the supported fourth exterior power of the actual
mass radical. Its `input_forbidden_iff` transfers prohibition from independently
defined original supported functionals to the supplied reference coefficients.
The gauge function takes values in the actual unbroken group `K`. An arbitrary
UV SU(6) lift is not such a function: it may fail to preserve the radical or
support. Lorentz and physical SM BNV identification remain application inputs.

## Ordered Pattern Assessment

| Pattern | Established result | Outstanding obligation |
| --- | --- | --- |
| Supplied homomorphic inner lift with the original source/charge certificates | Existing factorization and conditional proton-signature neutrality | Full coefficient/physical matching is not inferred from a signature |
| Ordinary complex-linear action inverting the specified SM probe | Excluded by positive actual-radical target and SM-cover character dictionary | Candidate behavior and dictionary must be proved |
| Pointwise inner lift without a homomorphic lift | Gauge removal and multiplication agreement on local coinvariants | Removed field maps need not form a representation; the earlier commuting charge theorem does not automatically apply |
| Non-reversing action gauge-equivalent to a genuine reference action on the relevant carrier | Same coefficient prohibition/nonzero behavior | Supply the reference action and prove gauge equivalence |
| Genuinely different induced coefficient action; UV lifts outside the unbroken group; general non-split extensions | Not classified by these tests | Construct an explicit candidate, its group law, actual light/SM dictionary and Lorentz/BNV support, then compute residual Hom |

These rows are conditional tests, not an exhaustive classification of SU(6)
automorphisms or extension groups. In particular, removing a gauge factor does
not make every non-split candidate equivalent to a previously excluded model.
There is still no constructed protecting solution.

## Verification

- Focused Math/GUT audit builds: 9 Math and 3 GUT strict transitive checks;
  only `propext`, `Classical.choice`, `Quot.sound` are allowed.
- `lake build Math.RepresentationTheory.Audit.AuditPointwiseGaugeRemoval
  GUT.SU6.SelectionRules.Audit.AuditGaugeEquivalentCandidate`: passed;
  the final GUT audit was rebuilt after adding original-input transfer.
- `lake build`: passed, 6,565 jobs on final source state.
- `node tools/layout/check-layout.mjs`: 1,238 modules passed.
- `node tools/docs/check-links.mjs`: 506 files, 3,333 local inline links,
  85 heading fragments, zero errors.
- `git diff --check`: passed. Focused checks emitted no warnings. Development
  errors in quotient extensionality, equivalence transport and the explicit
  supported carrier type were corrected without adding hypotheses.
- Pins and audit allowances are unchanged. No master integration is authorized.

## Next Scientific Input

The bounded sequential tests are complete. The unresolved route requires a
specific genuine action whose induced supported coefficient action is not
covered by the comparison test. A general automorphism/non-split classification
would be a new theorem-level prerequisite beyond the frozen scope. No such
classification or Lorentz/BNV realization is claimed in this checkpoint.

The subsequent [defect and conjugated-reversal tests](defect-result.md) close
specific conditional subcases of the outstanding field group-law and probe
behavior obligations. They do not supply the general classification above.
