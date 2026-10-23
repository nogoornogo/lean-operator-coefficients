import GUT.SU5.SelectionRules.SupportedTensors
import Math.RepresentationTheory.Decomposition.RepresentationDescent

open Physics

open Math

/-! The supported fields and ordered tensors descend to the actual SM
central quotient times the residual group, with exact covering pullback. -/

set_option autoImplicit false

-- Bounded instance-search budget for concrete transport/equivalence types.
set_option synthInstance.maxHeartbeats 200000

namespace GUT.SU5.SupportedQuotient

noncomputable section

open scoped TensorProduct

open MatterSource SupportedFields SupportedTensors StandardSMGaugeTensor StandardModelEmbedding
open FiniteAbelianChargeSectors StandardBranchProtonObstruction

variable {H : Type*} [CommGroup H] {n : ℕ} {R : OrdinaryAction H n}

def coverQuotient : GaugeGroup × H →* SMQuotient × H :=
  (QuotientGroup.mk' hom.ker).prodMap (MonoidHom.id H)

theorem coverQuotient_surjective : Function.Surjective (coverQuotient (H := H)) := by
  rintro ⟨q, h⟩
  induction q using QuotientGroup.induction_on with
  | H g => exact ⟨(g, h), rfl⟩

theorem mem_coverQuotient_ker (g : GaugeGroup × H) :
    g ∈ (coverQuotient (H := H)).ker ↔ g.1 ∈ hom.ker ∧ g.2 = 1 := by
  change (QuotientGroup.mk g.1, g.2) = (1, 1) ↔ _
  rw [Prod.mk.injEq, QuotientGroup.eq_one_iff]

theorem field_kernel {W : Type*} [AddCommGroup W] [Module ℂ W]
    {sigma : Representation ℂ GaugeGroup W} {chi : H →* Circle}
    (F : Realization R sigma chi) : coverQuotient.ker ≤ (fieldRepresentation F).ker := by
  intro g hg
  obtain ⟨hgauge, hres⟩ := (mem_coverQuotient_ker g).mp hg
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [fieldRepresentation_val, show hom g.1 = 1 from hgauge, hres]
  simp

def fieldAction {W : Type*} [AddCommGroup W] [Module ℂ W]
    {sigma : Representation ℂ GaugeGroup W} {chi : H →* Circle}
    (F : Realization R sigma chi) : Representation ℂ (SMQuotient × H) (Field F) :=
  RepresentationDescent.descend coverQuotient coverQuotient_surjective
    (fieldRepresentation F) (field_kernel F)

@[simp] theorem fieldAction_cover {W : Type*} [AddCommGroup W] [Module ℂ W]
    {sigma : Representation ℂ GaugeGroup W} {chi : H →* Circle}
    (F : Realization R sigma chi) (g : GaugeGroup × H) :
    fieldAction F (coverQuotient g) = fieldRepresentation F g :=
  RepresentationDescent.descend_apply _ _ _ _ g

theorem fieldAction_val {W : Type*} [AddCommGroup W] [Module ℂ W]
    {sigma : Representation ℂ GaugeGroup W} {chi : H →* Circle}
    (F : Realization R sigma chi) (q : SMQuotient) (h : H) (x : Field F) :
    (fieldAction F (q, h) x).val = (R h).val.val (MatterSource.gauge n (quotientHom q) x.val) := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    change (fieldAction F (coverQuotient (g, h)) x).val = _
    rw [fieldAction_cover, fieldRepresentation_val]
    rfl

variable {k : Charges (ChargeLabel H)}

theorem qque_kernel (S : Support R k) : coverQuotient.ker ≤ (qqueAction S).ker :=
  RepresentationDescent.kernel_tensor _ _
    (RepresentationDescent.kernel_tensor _ _ (field_kernel S.quark) _ (field_kernel S.quark)) _
    (RepresentationDescent.kernel_tensor _ _
      (RepresentationDescent.kernel_dual _ _ (field_kernel S.up)) _
      (RepresentationDescent.kernel_dual _ _ (field_kernel S.electron)))

theorem duql_kernel (S : Support R k) : coverQuotient.ker ≤ (duqlAction S).ker :=
  RepresentationDescent.kernel_tensor _ _
    (RepresentationDescent.kernel_tensor _ _
      (RepresentationDescent.kernel_dual _ _ (field_kernel S.down)) _
      (RepresentationDescent.kernel_dual _ _ (field_kernel S.up))) _
    (RepresentationDescent.kernel_tensor _ _ (field_kernel S.quark) _ (field_kernel S.lepton))

def quotientQQueAction (S : Support R k) : Representation ℂ (SMQuotient × H)
    ((Field S.quark ⊗[ℂ] Field S.quark) ⊗[ℂ]
      (Module.Dual ℂ (Field S.up) ⊗[ℂ] Module.Dual ℂ (Field S.electron))) :=
  RepresentationDescent.descend coverQuotient coverQuotient_surjective (qqueAction S) (qque_kernel S)

def quotientDuqlAction (S : Support R k) : Representation ℂ (SMQuotient × H)
    ((Module.Dual ℂ (Field S.down) ⊗[ℂ] Module.Dual ℂ (Field S.up)) ⊗[ℂ]
      (Field S.quark ⊗[ℂ] Field S.lepton)) :=
  RepresentationDescent.descend coverQuotient coverQuotient_surjective (duqlAction S) (duql_kernel S)

@[simp] theorem quotientQQueAction_cover (S : Support R k) (g : GaugeGroup × H) :
    quotientQQueAction S (coverQuotient g) = qqueAction S g :=
  RepresentationDescent.descend_apply _ _ _ _ g

@[simp] theorem quotientDuqlAction_cover (S : Support R k) (g : GaugeGroup × H) :
    quotientDuqlAction S (coverQuotient g) = duqlAction S g :=
  RepresentationDescent.descend_apply _ _ _ _ g

theorem qque_quotient_invariant (S : Support R k) (hk : SU5OrbitCompatible k) :
    ∀ g x, qqueTensor S (quotientQQueAction S g x) = qqueTensor S x :=
  RepresentationDescent.descend_invariant _ _ _ _ _ (qqueTensor_invariant S hk)

theorem duql_quotient_invariant (S : Support R k) (hk : SU5OrbitCompatible k) :
    ∀ g x, duqlTensor S (quotientDuqlAction S g x) = duqlTensor S x :=
  RepresentationDescent.descend_invariant _ _ _ _ _ (duqlTensor_invariant S hk)

end

end GUT.SU5.SupportedQuotient
