import GUT.SU6.Branching.StandardSMTorus
import GUT.SU6.Adapters.StandardSMContragredient

open Math

/-!
Persistent audit of the full-group standard restriction bridge.
This audits 6 and bar6; `AuditStandardSMUVMass` audits the exterior square.
-/

set_option autoImplicit false

namespace GUT.AuditStandardSMBranching

noncomputable section

open StandardSMGaugeTensor SMEpsilonTensor

def weakRotation : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  ⟨Matrix.of ![![0, 1], ![-1, 0]], by
    constructor
    · change Matrix.of ![![0, 1], ![-1, 0]] ∈ Matrix.unitaryGroup (Fin 2) ℂ
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_apply, Matrix.one_apply]
    · change Matrix.det (Matrix.of ![![0, 1], ![-1, 0]]) = 1
      norm_num [Matrix.det_fin_two]⟩

theorem off_diagonal_action :
    StandardSMGroup.splitEquiv
      (FundamentalRepresentation.rho (StandardSMGroup.hom (1, weakRotation, 1))
        ![0, 0, 0, 1, 0, 0]) = (0, (![0, -1], 0)) := by
  rw [StandardSMGroup.splitEquiv_action]
  apply Prod.ext
  · funext i
    fin_cases i <;>
      norm_num [StandardSMGroup.heavy, StandardSMGroup.splitEquiv, twist, color, phase]
  · apply Prod.ext
    · funext i
      fin_cases i <;>
        norm_num [StandardSMGroup.heavy, StandardSMGroup.splitEquiv, twist, weak, phase,
          weakRotation, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · rfl

example (H : Type*) [CommGroup H] : Representation.Equiv
    (ConcreteSU6Representations.fundamental.rho.comp (StandardSMGroup.withResidual H))
    (StandardSMFullGaugeMass.heavyRho H) := StandardSMGroup.neutralFundamentalEquiv H

example : Representation.Equiv
    (ConcreteSU6Representations.fundamental.rho.comp
      (StandardSMGroup.withResidual (Multiplicative (ZMod 2))))
    (StandardSMFullGaugeMass.heavyRho (Multiplicative (ZMod 2))) :=
  StandardSMGroup.neutralFundamentalEquiv _

example : Representation.Equiv
    (ConcreteSU6Representations.antifundamental.rho.comp StandardSMGroup.hom)
    StandardSMContragredient.antifundamentalSM := StandardSMContragredient.antifundamentalEquiv

#print axioms StandardSMGroup.continuousHom
#print axioms StandardSMGroup.fundamentalEquiv
#print axioms StandardSMGroup.analyticAntifundamentalEquiv
#print axioms StandardSMGroup.neutralFundamentalEquiv
#print axioms StandardSMTorus.hom_comp
#print axioms StandardSMTorus.continuous_hom
#print axioms StandardSMTorus.restrict_eq
#print axioms StandardSMTorus.withResidual_comp
#print axioms StandardSMTorus.covering_not_injective
#print axioms StandardSMContragredient.leptonDualEquiv
#print axioms StandardSMContragredient.antifundamentalEquiv
#print axioms SplitRepresentationProjection.dual_comp
#print axioms SplitRepresentationProjection.dualProdEquiv
#print axioms SplitRepresentationProjection.prodEquiv
#print axioms off_diagonal_action

end

end GUT.AuditStandardSMBranching
