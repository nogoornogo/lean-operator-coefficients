import Physics.StandardModel.Gauge.Charges.HyperchargeTensorTransport
import Physics.StandardModel.Gauge.Tensors.WeakContragredient
import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenLocal
import Math.RepresentationTheory.Coefficients.InvariantCoefficientTransport

open Math

/-! Charge-preserving gauge transports for dimension-seven typed patterns. -/
namespace Physics.BnvSevenGaugeTransport
set_option autoImplicit false
noncomputable section
open Representation StandardSMGaugeTensor StandardSMContragredient ExternalInvariantTensor

def antiLepton : Representation.Equiv StandardSMGaugeTensor.lepton.dual (twist weak 3) :=
  (chargedWeakDualEquiv 3).symm

def antiHiggs : Representation.Equiv (twist weak 3).dual (twist weak (-3)) := by
  have e := (chargedWeakDualEquiv (-3)).symm
  norm_num only [neg_neg] at e
  exact e

def antiElectron : Representation.Equiv electronRight.dual
    (twist (Representation.trivial ℂ GaugeGroup ℂ) 6) := by
  have e := HyperchargeTensorTransport.dualLine (-6)
  norm_num only [neg_neg] at e
  exact e

def uddRepresentation := ((upRight.tprod downRight).tprod
  (downRight.tprod StandardSMGaugeTensor.lepton.dual)).tprod (twist weak 3).dual

def dddRepresentation := ((downRight.tprod downRight).tprod
  (downRight.tprod StandardSMGaugeTensor.lepton.dual)).tprod (twist weak 3)

def neutralRepresentation := ((color.tprod color).tprod (color.tprod weak)).tprod weak

def qddRepresentation := ((quark.tprod downRight).tprod
  (downRight.tprod electronRight.dual)).tprod (twist weak 3).dual

def qddNeutral := (((color.tprod weak).tprod color).tprod
  (color.tprod (Representation.trivial ℂ GaugeGroup ℂ))).tprod weak

def qdd : Representation.Equiv qddRepresentation qddNeutral :=
  (tensorEquiv (tensorEquiv (Representation.Equiv.refl _)
    (tensorEquiv (Representation.Equiv.refl _) antiElectron)) antiHiggs).trans
    (HyperchargeTensorTransport.fiveNeutral (color.tprod weak) color color
      (Representation.trivial ℂ GaugeGroup ℂ) weak 1 (-2) (-2) 6 (-3) (by norm_num))

def moveWeak : Representation.Equiv ((color.tprod weak).tprod color)
    ((color.tprod color).tprod weak) :=
  (Representation.TensorProduct.assoc color weak color).trans
    ((tensorEquiv (Representation.Equiv.refl color)
      (Representation.TensorProduct.comm weak color)).trans
      (Representation.TensorProduct.assoc color color weak).symm)

def regroupQdd : Representation.Equiv qddNeutral
    (((color.tprod color).tprod color).tprod (weak.tprod weak)) :=
  (tensorEquiv (tensorEquiv moveWeak (Representation.TensorProduct.rid ℂ color))
    (Representation.Equiv.refl weak)).trans
    ((tensorEquiv
      ((Representation.TensorProduct.assoc (color.tprod color) weak color).trans
        ((tensorEquiv (Representation.Equiv.refl (color.tprod color))
          (Representation.TensorProduct.comm weak color)).trans
          (Representation.TensorProduct.assoc (color.tprod color) color weak).symm))
      (Representation.Equiv.refl weak)).trans
      (Representation.TensorProduct.assoc ((color.tprod color).tprod color) weak weak))

def qqdRepresentation := ((quark.tprod quark).tprod
  (downRight.tprod StandardSMGaugeTensor.lepton.dual)).tprod (twist weak 3).dual

def fourWeakNeutral := (((color.tprod weak).tprod (color.tprod weak)).tprod
  (color.tprod weak)).tprod weak

def qqd : Representation.Equiv qqdRepresentation fourWeakNeutral :=
  (tensorEquiv (tensorEquiv (Representation.Equiv.refl _)
      (tensorEquiv (Representation.Equiv.refl _) antiLepton)) antiHiggs).trans
    (HyperchargeTensorTransport.fiveNeutral (color.tprod weak) (color.tprod weak)
      color weak weak 1 1 (-2) 3 (-3) (by norm_num))

def regroupFourWeak : Representation.Equiv fourWeakNeutral
    (((color.tprod color).tprod color).tprod ((weak.tprod weak).tprod (weak.tprod weak))) :=
  (tensorEquiv (tensorEquiv (regroupPairDiagonal color color weak weak)
      (Representation.Equiv.refl (color.tprod weak))) (Representation.Equiv.refl weak)).trans
    ((tensorEquiv (regroupPairDiagonal (color.tprod color) color (weak.tprod weak) weak)
      (Representation.Equiv.refl weak)).trans
      ((Representation.TensorProduct.assoc ((color.tprod color).tprod color)
        ((weak.tprod weak).tprod weak) weak).trans
        (tensorEquiv (Representation.Equiv.refl ((color.tprod color).tprod color))
          (Representation.TensorProduct.assoc (weak.tprod weak) weak weak))))

def udd : Representation.Equiv uddRepresentation neutralRepresentation :=
  (tensorEquiv (tensorEquiv (Representation.Equiv.refl _)
      (tensorEquiv (Representation.Equiv.refl _) antiLepton)) antiHiggs).trans
    (HyperchargeTensorTransport.fiveNeutral color color color weak weak
      4 (-2) (-2) 3 (-3) (by norm_num))

def ddd : Representation.Equiv dddRepresentation neutralRepresentation :=
  (tensorEquiv (tensorEquiv (Representation.Equiv.refl _)
      (tensorEquiv (Representation.Equiv.refl _) antiLepton))
      (Representation.Equiv.refl _)).trans
    (HyperchargeTensorTransport.fiveNeutral color color color weak weak
      (-2) (-2) (-2) 3 3 (by norm_num))

def regroup : Representation.Equiv neutralRepresentation
    (((color.tprod color).tprod color).tprod (weak.tprod weak)) :=
  (tensorEquiv (Representation.TensorProduct.assoc (color.tprod color) color weak).symm
    (Representation.Equiv.refl weak)).trans
    (Representation.TensorProduct.assoc ((color.tprod color).tprod color) weak weak)

def cover : GaugeGroup →* (Matrix.specialUnitaryGroup (Fin 3) ℂ ×
    Matrix.specialUnitaryGroup (Fin 2) ℂ) where
  toFun g := (g.1, g.2.1)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem cover_surjective : Function.Surjective cover := by
  intro g
  exact ⟨(g.1, g.2, 1), rfl⟩

def core : Representation.Equiv
    (((color.tprod color).tprod color).tprod (weak.tprod weak))
    (BnvSevenLocal.gaugeRepresentation.comp cover) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' g := by
    ext a b c u v
    rfl

def fourWeakCore : Representation.Equiv
    (((color.tprod color).tprod color).tprod ((weak.tprod weak).tprod (weak.tprod weak)))
    (BnvSevenLocal.fourWeakGaugeRepresentation.comp cover) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' g := by
    ext a b c u v w x
    rfl

def qqdCore : Representation.Equiv qqdRepresentation
    (BnvSevenLocal.fourWeakGaugeRepresentation.comp cover) :=
  qqd.trans (regroupFourWeak.trans fourWeakCore)

def qqdInvariantEquiv : InvariantCoefficientTransport.Invariants qqdRepresentation ≃ₗ[ℂ]
    InvariantCoefficientTransport.Invariants BnvSevenLocal.fourWeakGaugeRepresentation :=
  (InvariantCoefficientTransport.alongEquiv qqdCore).trans
    (InvariantCoefficientTransport.alongSurjection BnvSevenLocal.fourWeakGaugeRepresentation
      cover cover_surjective)

def qqdPairing (i : Fin 2) := qqdInvariantEquiv.symm (BnvSevenLocal.fourWeakGaugePairing i)
def qqdProbe (i : Fin 2) := qqdCore.symm (BnvSevenLocal.fourWeakGaugeProbe i)

theorem qqd_reconstruction (f : InvariantCoefficientTransport.Invariants qqdRepresentation) :
    f = ∑ i, f (qqdProbe i) • qqdPairing i := by
  apply qqdInvariantEquiv.injective
  rw [map_sum]
  simp only [map_smul]
  calc
    _ = ∑ i, (qqdInvariantEquiv f) (BnvSevenLocal.fourWeakGaugeProbe i) •
        BnvSevenLocal.fourWeakGaugePairing i :=
      BnvSevenLocal.fourWeakGauge_reconstruction (qqdInvariantEquiv f)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show qqdInvariantEquiv (qqdPairing i) = BnvSevenLocal.fourWeakGaugePairing i
        from qqdInvariantEquiv.apply_symm_apply _]
      rfl

def uddCore : Representation.Equiv uddRepresentation
    (BnvSevenLocal.gaugeRepresentation.comp cover) := udd.trans (regroup.trans core)

def qddCore : Representation.Equiv qddRepresentation
    (BnvSevenLocal.gaugeRepresentation.comp cover) := qdd.trans (regroupQdd.trans core)

def qddInvariantEquiv : InvariantCoefficientTransport.Invariants qddRepresentation ≃ₗ[ℂ]
    InvariantCoefficientTransport.Invariants BnvSevenLocal.gaugeRepresentation :=
  (InvariantCoefficientTransport.alongEquiv qddCore).trans
    (InvariantCoefficientTransport.alongSurjection BnvSevenLocal.gaugeRepresentation
      cover cover_surjective)

def qddPairing := qddInvariantEquiv.symm BnvSevenLocal.gaugePairing
def qddProbe := qddCore.symm BnvSevenLocal.gaugeProbe

theorem qdd_unique (f : InvariantCoefficientTransport.Invariants qddRepresentation) :
    f = f qddProbe • qddPairing := by
  apply qddInvariantEquiv.injective
  rw [map_smul]
  rw [show qddInvariantEquiv qddPairing = BnvSevenLocal.gaugePairing from
    qddInvariantEquiv.apply_symm_apply _]
  exact BnvSevenLocal.gauge_unique (qddInvariantEquiv f)

def dddCore : Representation.Equiv dddRepresentation
    (BnvSevenLocal.gaugeRepresentation.comp cover) := ddd.trans (regroup.trans core)

def uddInvariantEquiv : InvariantCoefficientTransport.Invariants uddRepresentation ≃ₗ[ℂ]
    InvariantCoefficientTransport.Invariants BnvSevenLocal.gaugeRepresentation :=
  (InvariantCoefficientTransport.alongEquiv uddCore).trans
    (InvariantCoefficientTransport.alongSurjection BnvSevenLocal.gaugeRepresentation
      cover cover_surjective)

def dddInvariantEquiv : InvariantCoefficientTransport.Invariants dddRepresentation ≃ₗ[ℂ]
    InvariantCoefficientTransport.Invariants BnvSevenLocal.gaugeRepresentation :=
  (InvariantCoefficientTransport.alongEquiv dddCore).trans
    (InvariantCoefficientTransport.alongSurjection BnvSevenLocal.gaugeRepresentation
      cover cover_surjective)

def uddPairing := uddInvariantEquiv.symm BnvSevenLocal.gaugePairing
def dddPairing := dddInvariantEquiv.symm BnvSevenLocal.gaugePairing
def uddProbe := uddCore.symm BnvSevenLocal.gaugeProbe
def dddProbe := dddCore.symm BnvSevenLocal.gaugeProbe

theorem udd_unique (f : InvariantCoefficientTransport.Invariants uddRepresentation) :
    f = f uddProbe • uddPairing := by
  apply uddInvariantEquiv.injective
  rw [map_smul]
  have hp : uddInvariantEquiv uddPairing = BnvSevenLocal.gaugePairing :=
    uddInvariantEquiv.apply_symm_apply _
  rw [hp]
  exact BnvSevenLocal.gauge_unique (uddInvariantEquiv f)

theorem ddd_unique (f : InvariantCoefficientTransport.Invariants dddRepresentation) :
    f = f dddProbe • dddPairing := by
  apply dddInvariantEquiv.injective
  rw [map_smul]
  have hp : dddInvariantEquiv dddPairing = BnvSevenLocal.gaugePairing :=
    dddInvariantEquiv.apply_symm_apply _
  rw [hp]
  exact BnvSevenLocal.gauge_unique (dddInvariantEquiv f)

end
end Physics.BnvSevenGaugeTransport
