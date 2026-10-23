import Physics.StandardModel.Operators.Support.Quark.SMQLPatternRequests
import Physics.StandardModel.Operators.SMQLCompactMultiplicity
import Physics.StandardModel.Operators.SMFiniteSupportTable
import Physics.StandardModel.Operators.ProhibitionPatterns
import Math.LinearAlgebra.MixedSelectionRequests
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Quark.SMQLPatternRequests instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMQLPatternRequests.Coefficients => Physics.SMQLPatternRequests.Coefficients,
  GUT.SMQLPatternRequests.Conditions => Physics.SMQLPatternRequests.Conditions,
  GUT.SMQLPatternRequests.Conditions.eq_1 => Physics.SMQLPatternRequests.Conditions.eq_1,
  GUT.SMQLPatternRequests.Domain => Physics.SMQLPatternRequests.Domain,
  GUT.SMQLPatternRequests.Entries => Physics.SMQLPatternRequests.Entries,
  GUT.SMQLPatternRequests.EntryAllowed => Physics.SMQLPatternRequests.EntryAllowed,
  GUT.SMQLPatternRequests.EntryAllowed.congr_simp => Physics.SMQLPatternRequests.EntryAllowed.congr_simp,
  GUT.SMQLPatternRequests.Index => Physics.SMQLPatternRequests.Index,
  GUT.SMQLPatternRequests.OriginalAllowed => Physics.SMQLPatternRequests.OriginalAllowed,
  GUT.SMQLPatternRequests.OriginalAllowed.congr_simp => Physics.SMQLPatternRequests.OriginalAllowed.congr_simp,
  GUT.SMQLPatternRequests.OriginalAllowed.eq_1 => Physics.SMQLPatternRequests.OriginalAllowed.eq_1,
  GUT.SMQLPatternRequests.OriginalForbidden => Physics.SMQLPatternRequests.OriginalForbidden,
  GUT.SMQLPatternRequests.OriginalForbidden.congr_simp => Physics.SMQLPatternRequests.OriginalForbidden.congr_simp,
  GUT.SMQLPatternRequests.OriginalForbidden.eq_1 => Physics.SMQLPatternRequests.OriginalForbidden.eq_1,
  GUT.SMQLPatternRequests.ReductionInput => Physics.SMQLPatternRequests.ReductionInput,
  GUT.SMQLPatternRequests.Request => Physics.SMQLPatternRequests.Request,
  GUT.SMQLPatternRequests.Satisfies => Physics.SMQLPatternRequests.Satisfies,
  GUT.SMQLPatternRequests.Target => Physics.SMQLPatternRequests.Target,
  GUT.SMQLPatternRequests.Valid => Physics.SMQLPatternRequests.Valid,
  GUT.SMQLPatternRequests.allow_of_entry => Physics.SMQLPatternRequests.allow_of_entry,
  GUT.SMQLPatternRequests.allowed_iff => Physics.SMQLPatternRequests.allowed_iff,
  GUT.SMQLPatternRequests.allowed_iff_original => Physics.SMQLPatternRequests.allowed_iff_original,
  GUT.SMQLPatternRequests.b1ForbiddenB2Allowed => Physics.SMQLPatternRequests.b1ForbiddenB2Allowed,
  GUT.SMQLPatternRequests.b1ForbiddenB2Allowed.eq_1 => Physics.SMQLPatternRequests.b1ForbiddenB2Allowed.eq_1,
  GUT.SMQLPatternRequests.b1_b2_iff => Physics.SMQLPatternRequests.b1_b2_iff,
  GUT.SMQLPatternRequests.b1_b2_original_iff => Physics.SMQLPatternRequests.b1_b2_original_iff,
  GUT.SMQLPatternRequests.blCharge => Physics.SMQLPatternRequests.blCharge,
  GUT.SMQLPatternRequests.entry_allowed_iff => Physics.SMQLPatternRequests.entry_allowed_iff,
  GUT.SMQLPatternRequests.entry_original => Physics.SMQLPatternRequests.entry_original,
  GUT.SMQLPatternRequests.forbid_of_charge => Physics.SMQLPatternRequests.forbid_of_charge,
  GUT.SMQLPatternRequests.forbidden_iff => Physics.SMQLPatternRequests.forbidden_iff,
  GUT.SMQLPatternRequests.forbidden_iff_original => Physics.SMQLPatternRequests.forbidden_iff_original,
  GUT.SMQLPatternRequests.instFintypeEntries => Physics.SMQLPatternRequests.instFintypeEntries,
  GUT.SMQLPatternRequests.original_request_iff => Physics.SMQLPatternRequests.original_request_iff,
  GUT.SMQLPatternRequests.satisfies_iff => Physics.SMQLPatternRequests.satisfies_iff,
  GUT.SMQLPatternRequests.selector_matches_existing => Physics.SMQLPatternRequests.selector_matches_existing
]

assert_compatible GUT.SMQLPatternRequests.Coefficients => Physics.SMQLPatternRequests.Coefficients
assert_compatible GUT.SMQLPatternRequests.Conditions => Physics.SMQLPatternRequests.Conditions
assert_compatible GUT.SMQLPatternRequests.Conditions.eq_1 => Physics.SMQLPatternRequests.Conditions.eq_1
assert_compatible GUT.SMQLPatternRequests.Domain => Physics.SMQLPatternRequests.Domain
assert_compatible GUT.SMQLPatternRequests.Entries => Physics.SMQLPatternRequests.Entries
assert_compatible GUT.SMQLPatternRequests.EntryAllowed => Physics.SMQLPatternRequests.EntryAllowed
assert_compatible GUT.SMQLPatternRequests.EntryAllowed.congr_simp => Physics.SMQLPatternRequests.EntryAllowed.congr_simp
assert_compatible GUT.SMQLPatternRequests.Index => Physics.SMQLPatternRequests.Index
assert_compatible GUT.SMQLPatternRequests.OriginalAllowed => Physics.SMQLPatternRequests.OriginalAllowed
assert_compatible GUT.SMQLPatternRequests.OriginalAllowed.congr_simp => Physics.SMQLPatternRequests.OriginalAllowed.congr_simp
assert_compatible GUT.SMQLPatternRequests.OriginalAllowed.eq_1 => Physics.SMQLPatternRequests.OriginalAllowed.eq_1
assert_compatible GUT.SMQLPatternRequests.OriginalForbidden => Physics.SMQLPatternRequests.OriginalForbidden
assert_compatible GUT.SMQLPatternRequests.OriginalForbidden.congr_simp => Physics.SMQLPatternRequests.OriginalForbidden.congr_simp
assert_compatible GUT.SMQLPatternRequests.OriginalForbidden.eq_1 => Physics.SMQLPatternRequests.OriginalForbidden.eq_1
assert_compatible GUT.SMQLPatternRequests.ReductionInput => Physics.SMQLPatternRequests.ReductionInput
assert_compatible GUT.SMQLPatternRequests.Request => Physics.SMQLPatternRequests.Request
assert_compatible GUT.SMQLPatternRequests.Satisfies => Physics.SMQLPatternRequests.Satisfies
assert_compatible GUT.SMQLPatternRequests.Target => Physics.SMQLPatternRequests.Target
assert_compatible GUT.SMQLPatternRequests.Valid => Physics.SMQLPatternRequests.Valid
assert_compatible GUT.SMQLPatternRequests.allow_of_entry => Physics.SMQLPatternRequests.allow_of_entry
assert_compatible GUT.SMQLPatternRequests.allowed_iff => Physics.SMQLPatternRequests.allowed_iff
assert_compatible GUT.SMQLPatternRequests.allowed_iff_original => Physics.SMQLPatternRequests.allowed_iff_original
assert_compatible GUT.SMQLPatternRequests.b1ForbiddenB2Allowed => Physics.SMQLPatternRequests.b1ForbiddenB2Allowed
assert_compatible GUT.SMQLPatternRequests.b1ForbiddenB2Allowed.eq_1 => Physics.SMQLPatternRequests.b1ForbiddenB2Allowed.eq_1
assert_compatible GUT.SMQLPatternRequests.b1_b2_iff => Physics.SMQLPatternRequests.b1_b2_iff
assert_compatible GUT.SMQLPatternRequests.b1_b2_original_iff => Physics.SMQLPatternRequests.b1_b2_original_iff
assert_compatible GUT.SMQLPatternRequests.blCharge => Physics.SMQLPatternRequests.blCharge
assert_compatible GUT.SMQLPatternRequests.entry_allowed_iff => Physics.SMQLPatternRequests.entry_allowed_iff
assert_compatible GUT.SMQLPatternRequests.entry_original => Physics.SMQLPatternRequests.entry_original
assert_compatible GUT.SMQLPatternRequests.forbid_of_charge => Physics.SMQLPatternRequests.forbid_of_charge
assert_compatible GUT.SMQLPatternRequests.forbidden_iff => Physics.SMQLPatternRequests.forbidden_iff
assert_compatible GUT.SMQLPatternRequests.forbidden_iff_original => Physics.SMQLPatternRequests.forbidden_iff_original
assert_compatible GUT.SMQLPatternRequests.instFintypeEntries => Physics.SMQLPatternRequests.instFintypeEntries
assert_compatible GUT.SMQLPatternRequests.original_request_iff => Physics.SMQLPatternRequests.original_request_iff
assert_compatible GUT.SMQLPatternRequests.satisfies_iff => Physics.SMQLPatternRequests.satisfies_iff
assert_compatible GUT.SMQLPatternRequests.selector_matches_existing => Physics.SMQLPatternRequests.selector_matches_existing
