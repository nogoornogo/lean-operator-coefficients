import Physics.StandardModel.Operators.BaryonOne.Qque.Audit.AuditQqueCommonIrreducible
import Physics.StandardModel.Operators.QqueCommonIrreducible
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.Audit.AuditQqueCommonIrreducible instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.QqueCommonIrreducibleAudit.coefficient => Physics.QqueCommonIrreducibleAudit.coefficient,
  GUT.QqueCommonIrreducibleAudit.coefficient.eq_1 => Physics.QqueCommonIrreducibleAudit.coefficient.eq_1,
  GUT.QqueCommonIrreducibleAudit.e => Physics.QqueCommonIrreducibleAudit.e,
  GUT.QqueCommonIrreducibleAudit.e.eq_1 => Physics.QqueCommonIrreducibleAudit.e.eq_1,
  GUT.QqueCommonIrreducibleAudit.exists_hom => Physics.QqueCommonIrreducibleAudit.exists_hom,
  GUT.QqueCommonIrreducibleAudit.exterior_nonzero => Physics.QqueCommonIrreducibleAudit.exterior_nonzero,
  GUT.QqueCommonIrreducibleAudit.no_q_up_map => Physics.QqueCommonIrreducibleAudit.no_q_up_map,
  GUT.QqueCommonIrreducibleAudit.no_q_up_overlap => Physics.QqueCommonIrreducibleAudit.no_q_up_overlap,
  GUT.QqueCommonIrreducibleAudit.post_product_overlap => Physics.QqueCommonIrreducibleAudit.post_product_overlap,
  GUT.QqueCommonIrreducibleAudit.product => Physics.QqueCommonIrreducibleAudit.product,
  GUT.QqueCommonIrreducibleAudit.product_apply => Physics.QqueCommonIrreducibleAudit.product_apply,
  GUT.QqueCommonIrreducibleAudit.q => Physics.QqueCommonIrreducibleAudit.q,
  GUT.QqueCommonIrreducibleAudit.q.eq_1 => Physics.QqueCommonIrreducibleAudit.q.eq_1,
  GUT.QqueCommonIrreducibleAudit.q_continuous => Physics.QqueCommonIrreducibleAudit.q_continuous,
  GUT.QqueCommonIrreducibleAudit.u => Physics.QqueCommonIrreducibleAudit.u,
  GUT.QqueCommonIrreducibleAudit.u.eq_1 => Physics.QqueCommonIrreducibleAudit.u.eq_1
]

assert_compatible GUT.QqueCommonIrreducibleAudit.coefficient => Physics.QqueCommonIrreducibleAudit.coefficient
assert_compatible GUT.QqueCommonIrreducibleAudit.coefficient.eq_1 => Physics.QqueCommonIrreducibleAudit.coefficient.eq_1
assert_compatible GUT.QqueCommonIrreducibleAudit.e => Physics.QqueCommonIrreducibleAudit.e
assert_compatible GUT.QqueCommonIrreducibleAudit.e.eq_1 => Physics.QqueCommonIrreducibleAudit.e.eq_1
assert_compatible GUT.QqueCommonIrreducibleAudit.exists_hom => Physics.QqueCommonIrreducibleAudit.exists_hom
assert_compatible GUT.QqueCommonIrreducibleAudit.exterior_nonzero => Physics.QqueCommonIrreducibleAudit.exterior_nonzero
assert_compatible GUT.QqueCommonIrreducibleAudit.no_q_up_map => Physics.QqueCommonIrreducibleAudit.no_q_up_map
assert_compatible GUT.QqueCommonIrreducibleAudit.no_q_up_overlap => Physics.QqueCommonIrreducibleAudit.no_q_up_overlap
assert_compatible GUT.QqueCommonIrreducibleAudit.post_product_overlap => Physics.QqueCommonIrreducibleAudit.post_product_overlap
assert_compatible GUT.QqueCommonIrreducibleAudit.product => Physics.QqueCommonIrreducibleAudit.product
assert_compatible GUT.QqueCommonIrreducibleAudit.product_apply => Physics.QqueCommonIrreducibleAudit.product_apply
assert_compatible GUT.QqueCommonIrreducibleAudit.q => Physics.QqueCommonIrreducibleAudit.q
assert_compatible GUT.QqueCommonIrreducibleAudit.q.eq_1 => Physics.QqueCommonIrreducibleAudit.q.eq_1
assert_compatible GUT.QqueCommonIrreducibleAudit.q_continuous => Physics.QqueCommonIrreducibleAudit.q_continuous
assert_compatible GUT.QqueCommonIrreducibleAudit.u => Physics.QqueCommonIrreducibleAudit.u
assert_compatible GUT.QqueCommonIrreducibleAudit.u.eq_1 => Physics.QqueCommonIrreducibleAudit.u.eq_1
