import Physics.StandardModel.Operators.Support.Dimension.SMB1BelowTenAssignments
import Physics.StandardModel.Operators.SMB1BelowTen
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Dimension.SMB1BelowTenAssignments instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMB1BelowTen.Allowed.congr_simp => Physics.SMB1BelowTen.Allowed.congr_simp,
  GUT.SMB1BelowTen.Forbidden.congr_simp => Physics.SMB1BelowTen.Forbidden.congr_simp,
  GUT.SMB1BelowTenAssignments.allDegreeForbiddenCount => Physics.SMB1BelowTenAssignments.allDegreeForbiddenCount,
  GUT.SMB1BelowTenAssignments.all_degree_forbidden_semantics => Physics.SMB1BelowTenAssignments.all_degree_forbidden_semantics,
  GUT.SMB1BelowTenAssignments.allowedCount => Physics.SMB1BelowTenAssignments.allowedCount,
  GUT.SMB1BelowTenAssignments.check => Physics.SMB1BelowTenAssignments.check,
  GUT.SMB1BelowTenAssignments.check.eq_1 => Physics.SMB1BelowTenAssignments.check.eq_1,
  GUT.SMB1BelowTenAssignments.counts => Physics.SMB1BelowTenAssignments.counts,
  GUT.SMB1BelowTenAssignments.coverage => Physics.SMB1BelowTenAssignments.coverage,
  GUT.SMB1BelowTenAssignments.domain_allowed_iff => Physics.SMB1BelowTenAssignments.domain_allowed_iff,
  GUT.SMB1BelowTenAssignments.domain_nonzero => Physics.SMB1BelowTenAssignments.domain_nonzero,
  GUT.SMB1BelowTenAssignments.exhaustive_count => Physics.SMB1BelowTenAssignments.exhaustive_count,
  GUT.SMB1BelowTenAssignments.forbiddenCount => Physics.SMB1BelowTenAssignments.forbiddenCount,
  GUT.SMB1BelowTenAssignments.laterAllowedCount => Physics.SMB1BelowTenAssignments.laterAllowedCount,
  GUT.SMB1BelowTenAssignments.later_allowed_semantics => Physics.SMB1BelowTenAssignments.later_allowed_semantics,
  GUT.SMB1BelowTenAssignments.row_allowed_iff => Physics.SMB1BelowTenAssignments.row_allowed_iff,
  GUT.SMB1BelowTenAssignments.row_decision => Physics.SMB1BelowTenAssignments.row_decision,
  GUT.SMB1BelowTenAssignments.row_forbidden_iff => Physics.SMB1BelowTenAssignments.row_forbidden_iff
]

assert_compatible GUT.SMB1BelowTen.Allowed.congr_simp => Physics.SMB1BelowTen.Allowed.congr_simp
assert_compatible GUT.SMB1BelowTen.Forbidden.congr_simp => Physics.SMB1BelowTen.Forbidden.congr_simp
assert_compatible GUT.SMB1BelowTenAssignments.allDegreeForbiddenCount => Physics.SMB1BelowTenAssignments.allDegreeForbiddenCount
assert_compatible GUT.SMB1BelowTenAssignments.all_degree_forbidden_semantics => Physics.SMB1BelowTenAssignments.all_degree_forbidden_semantics
assert_compatible GUT.SMB1BelowTenAssignments.allowedCount => Physics.SMB1BelowTenAssignments.allowedCount
assert_compatible GUT.SMB1BelowTenAssignments.check => Physics.SMB1BelowTenAssignments.check
assert_compatible GUT.SMB1BelowTenAssignments.check.eq_1 => Physics.SMB1BelowTenAssignments.check.eq_1
assert_compatible GUT.SMB1BelowTenAssignments.counts => Physics.SMB1BelowTenAssignments.counts
assert_compatible GUT.SMB1BelowTenAssignments.coverage => Physics.SMB1BelowTenAssignments.coverage
assert_compatible GUT.SMB1BelowTenAssignments.domain_allowed_iff => Physics.SMB1BelowTenAssignments.domain_allowed_iff
assert_compatible GUT.SMB1BelowTenAssignments.domain_nonzero => Physics.SMB1BelowTenAssignments.domain_nonzero
assert_compatible GUT.SMB1BelowTenAssignments.exhaustive_count => Physics.SMB1BelowTenAssignments.exhaustive_count
assert_compatible GUT.SMB1BelowTenAssignments.forbiddenCount => Physics.SMB1BelowTenAssignments.forbiddenCount
assert_compatible GUT.SMB1BelowTenAssignments.laterAllowedCount => Physics.SMB1BelowTenAssignments.laterAllowedCount
assert_compatible GUT.SMB1BelowTenAssignments.later_allowed_semantics => Physics.SMB1BelowTenAssignments.later_allowed_semantics
assert_compatible GUT.SMB1BelowTenAssignments.row_allowed_iff => Physics.SMB1BelowTenAssignments.row_allowed_iff
assert_compatible GUT.SMB1BelowTenAssignments.row_decision => Physics.SMB1BelowTenAssignments.row_decision
assert_compatible GUT.SMB1BelowTenAssignments.row_forbidden_iff => Physics.SMB1BelowTenAssignments.row_forbidden_iff
