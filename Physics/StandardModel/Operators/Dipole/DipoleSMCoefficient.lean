import Physics.StandardModel.Operators.Dipole.DipoleCoefficientCompleteness

open Math

/-! Restore the full SM covering group and the actual species hypercharges.
The chosen pseudoreal Higgs coordinate is justified by weakDualEquiv. -/
namespace Physics.DipoleSMCoefficient
set_option autoImplicit false
noncomputable section
open Representation InvariantCoefficientTransport
open scoped TensorProduct

variable {H : Type*} [Group H]
abbrev FullGroup (H : Type*) := (StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) × H

def projection : FullGroup H →* (DipoleLocalSector.Group × H) where
  toFun g := ((g.1.1.2.1, g.1.2), g.2)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem projection_surjective : Function.Surjective (projection (H := H)) := by
  rintro ⟨⟨w,s⟩,h⟩
  exact ⟨(((1,(w,1)),s),h), rfl⟩

variable {V : Type*} [AddCommMonoid V] [Module ℂ V]

def charged (rho : Representation ℂ (DipoleLocalSector.Group × H) V) (y : ℤ) :
    Representation ℂ (FullGroup H) V where
  toFun g := StandardSMGaugeTensor.phase y g.1.1 • rho (projection g)
  map_one' := by simp
  map_mul' g h := by simp [smul_smul, mul_comm]

variable {L E S F : Type*}
  [AddCommMonoid L] [Module ℂ L] [AddCommMonoid E] [Module ℂ E]
  [AddCommMonoid S] [Module ℂ S] [AddCommMonoid F] [Module ℂ F]
  (l : Representation ℂ (DipoleLocalSector.Group × H) L)
  (e : Representation ℂ (DipoleLocalSector.Group × H) E)
  (s : Representation ℂ (DipoleLocalSector.Group × H) S)
  (f : Representation ℂ (DipoleLocalSector.Group × H) F)

def ordered := ((charged l (-3)).tprod (charged e 6)).tprod
  ((charged s (-3)).tprod (charged f 0))

def cancelCharges : Representation.Equiv (ordered l e s f)
    (((l.tprod e).tprod (s.tprod f)).comp projection) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' g := by
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext; intro x
    apply LinearMap.ext; intro y
    apply TensorProduct.ext
    apply LinearMap.ext; intro z
    apply LinearMap.ext; intro w
    change (((charged l (-3)) g x ⊗ₜ[ℂ] (charged e 6) g y) ⊗ₜ[ℂ]
      ((charged s (-3)) g z ⊗ₜ[ℂ] (charged f 0) g w)) =
      ((l (projection g) x ⊗ₜ[ℂ] e (projection g) y) ⊗ₜ[ℂ]
        (s (projection g) z ⊗ₜ[ℂ] f (projection g) w))
    have h0 : StandardSMGaugeTensor.phase 0 g.1.1 = 1 := by
      simp [StandardSMGaugeTensor.phase]
    change (((StandardSMGaugeTensor.phase (-3) g.1.1 • l (projection g) x) ⊗ₜ[ℂ]
      (StandardSMGaugeTensor.phase 6 g.1.1 • e (projection g) y)) ⊗ₜ[ℂ]
      ((StandardSMGaugeTensor.phase (-3) g.1.1 • s (projection g) z) ⊗ₜ[ℂ]
        (StandardSMGaugeTensor.phase 0 g.1.1 • f (projection g) w))) = _
    simp only [h0, one_smul,
      TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul]
    change (StandardSMGaugeTensor.phase (-3) g.1.1 *
      (StandardSMGaugeTensor.phase 6 g.1.1 * StandardSMGaugeTensor.phase (-3) g.1.1)) •
      ((l (projection g) x ⊗ₜ[ℂ] e (projection g) y) ⊗ₜ[ℂ]
        (s (projection g) z ⊗ₜ[ℂ] f (projection g) w)) = _
    rw [← mul_assoc, DipoleGaugeTensor.phases, one_smul]

def coefficientEquiv : Invariants (ordered l e s f) ≃ₗ[ℂ]
    Invariants ((l.tprod e).tprod (s.tprod f)) :=
  (alongEquiv (cancelCharges l e s f)).trans
    (alongSurjection ((l.tprod e).tprod (s.tprod f)) projection projection_surjective)

variable {A B : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]
  (a : Representation ℂ H A) (b : Representation ℂ H B)

def orderedB := ordered (DipoleCoefficientCompleteness.lepton a)
  (DipoleCoefficientCompleteness.electron b) DipoleCoefficientCompleteness.higgs
    DipoleCoefficientCompleteness.strengthB
def orderedW := ordered (DipoleCoefficientCompleteness.lepton a)
  (DipoleCoefficientCompleteness.electron b) DipoleCoefficientCompleteness.higgs
    DipoleCoefficientCompleteness.strengthW

abbrev SectorB := Invariants (orderedB a b)
abbrev SectorW := Invariants (orderedW a b)

variable [FiniteDimensional ℂ B]

def equivB : SectorB a b ≃ₗ[ℂ] IntertwiningMap a b :=
  (coefficientEquiv _ _ _ _).trans (DipoleCoefficientCompleteness.equivB a b)
def equivW : SectorW a b ≃ₗ[ℂ] IntertwiningMap a b :=
  (coefficientEquiv _ _ _ _).trans (DipoleCoefficientCompleteness.equivW a b)
def equiv : (SectorB a b × SectorW a b) ≃ₗ[ℂ]
    (IntertwiningMap a b × IntertwiningMap a b) :=
  LinearEquiv.prodCongr (equivB a b) (equivW a b)

theorem exists_nonzero_iff : (∃ c : SectorB a b × SectorW a b, c ≠ 0) ↔
    ∃ k : IntertwiningMap a b, k ≠ 0 := by
  let e : (SectorB a b × SectorW a b) ≃ₗ[ℂ]
      (DipoleCoefficientCompleteness.SectorB a b × DipoleCoefficientCompleteness.SectorW a b) :=
    LinearEquiv.prodCongr (coefficientEquiv _ _ _ _) (coefficientEquiv _ _ _ _)
  have he : (∃ c : SectorB a b × SectorW a b, c ≠ 0) ↔
      ∃ c : DipoleCoefficientCompleteness.SectorB a b ×
        DipoleCoefficientCompleteness.SectorW a b, c ≠ 0 := by
    constructor
    · rintro ⟨c,hc⟩
      exact ⟨e c, fun h => hc (e.injective (h.trans e.map_zero.symm))⟩
    · rintro ⟨c,hc⟩
      exact ⟨e.symm c, fun h => hc (e.symm.injective (h.trans e.symm.map_zero.symm))⟩
  exact he.trans (DipoleCoefficientCompleteness.exists_nonzero_iff a b)

variable {L' E' S' F' : Type*}
  [AddCommMonoid L'] [Module ℂ L'] [AddCommMonoid E'] [Module ℂ E']
  [AddCommMonoid S'] [Module ℂ S'] [AddCommMonoid F'] [Module ℂ F']
  (l' : Representation ℂ (FullGroup H) L') (e' : Representation ℂ (FullGroup H) E')
  (s' : Representation ℂ (FullGroup H) S') (f' : Representation ℂ (FullGroup H) F')

/-- Actual fields are supplied only with species identifications; no coefficient
or generation mechanism is an input to this completeness equivalence. -/
def onFieldsB
    (el : Representation.Equiv l' (charged (DipoleCoefficientCompleteness.lepton a) (-3)))
    (ee : Representation.Equiv e' (charged (DipoleCoefficientCompleteness.electron b) 6))
    (es : Representation.Equiv s' (charged DipoleCoefficientCompleteness.higgs (-3)))
    (ef : Representation.Equiv f' (charged DipoleCoefficientCompleteness.strengthB 0)) :
    Invariants ((l'.tprod e').tprod (s'.tprod f')) ≃ₗ[ℂ] IntertwiningMap a b :=
  (alongEquiv (ExternalInvariantTensor.tensorEquiv
    (ExternalInvariantTensor.tensorEquiv el ee) (ExternalInvariantTensor.tensorEquiv es ef))).trans
    (equivB a b)

def onFieldsW
    (el : Representation.Equiv l' (charged (DipoleCoefficientCompleteness.lepton a) (-3)))
    (ee : Representation.Equiv e' (charged (DipoleCoefficientCompleteness.electron b) 6))
    (es : Representation.Equiv s' (charged DipoleCoefficientCompleteness.higgs (-3)))
    (ef : Representation.Equiv f' (charged DipoleCoefficientCompleteness.strengthW 0)) :
    Invariants ((l'.tprod e').tprod (s'.tprod f')) ≃ₗ[ℂ] IntertwiningMap a b :=
  (alongEquiv (ExternalInvariantTensor.tensorEquiv
    (ExternalInvariantTensor.tensorEquiv el ee) (ExternalInvariantTensor.tensorEquiv es ef))).trans
    (equivW a b)

end
end Physics.DipoleSMCoefficient
