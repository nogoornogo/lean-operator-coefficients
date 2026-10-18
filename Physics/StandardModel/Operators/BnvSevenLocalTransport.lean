import Physics.StandardModel.Operators.BnvSevenFieldTensor
import Physics.StandardModel.Operators.BnvSevenGaugeTransport

open Math

/-! Actual positive dimension-seven gauge/Weyl tensors transported to the
independently classified local cores. -/
namespace GUT.BnvSevenLocalTransport
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor BnvSevenPatternDescent
open scoped TensorProduct

abbrev WeakCoreCarrier : Fin 4 → Type
  | 0 => SMEpsilonTensor.Weak ⊗[ℂ] SMEpsilonTensor.Weak
  | 1 => (SMEpsilonTensor.Weak ⊗[ℂ] SMEpsilonTensor.Weak) ⊗[ℂ]
      (SMEpsilonTensor.Weak ⊗[ℂ] SMEpsilonTensor.Weak)
  | 2 => SMEpsilonTensor.Weak ⊗[ℂ] SMEpsilonTensor.Weak
  | 3 => SMEpsilonTensor.Weak ⊗[ℂ] SMEpsilonTensor.Weak

instance (p : Fin 4) : AddCommGroup (WeakCoreCarrier p) := match p with
  | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance | 3 => inferInstance
instance (p : Fin 4) : Module ℂ (WeakCoreCarrier p) := match p with
  | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance | 3 => inferInstance

abbrev GaugeCoreCarrier (p : Fin 4) :=
  ((SMEpsilonTensor.Color ⊗[ℂ] SMEpsilonTensor.Color) ⊗[ℂ] SMEpsilonTensor.Color) ⊗[ℂ]
    WeakCoreCarrier p

def gaugeCore (p : Fin 4) : Representation ℂ
    (Matrix.specialUnitaryGroup (Fin 3) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (GaugeCoreCarrier p) := match p with
  | 0 => BnvSevenLocal.gaugeRepresentation
  | 1 => BnvSevenLocal.fourWeakGaugeRepresentation
  | 2 => BnvSevenLocal.gaugeRepresentation
  | 3 => BnvSevenLocal.gaugeRepresentation

def spinCore (p : Fin 4) := match p with
  | 0 => FourSameWeylCompleteness.representation true
  | 1 => DuqlOrderedCompleteness.spin
  | 2 => DuqlOrderedCompleteness.spin
  | 3 => FourSameWeylCompleteness.representation true

def gaugeEquiv (p : Fin 4) : Representation.Equiv
    (BnvSevenFieldTensor.gaugeTensor (pattern p) (scalar p))
    ((gaugeCore p).comp BnvSevenGaugeTransport.cover) := match p with
  | 0 => BnvSevenGaugeTransport.uddCore
  | 1 => BnvSevenGaugeTransport.qqdCore
  | 2 => BnvSevenGaugeTransport.qddCore
  | 3 => BnvSevenGaugeTransport.dddCore

def qddSpin : Representation.Equiv
    ((WeylSpinor.left.tprod WeylSpinor.right).tprod
      (WeylSpinor.right.tprod WeylSpinor.left)) DuqlOrderedCompleteness.spin :=
  (tensorEquiv (Representation.TensorProduct.comm WeylSpinor.left WeylSpinor.right)
    (Representation.Equiv.refl (WeylSpinor.right.tprod WeylSpinor.left))).trans
      (regroupPairDiagonal WeylSpinor.right WeylSpinor.right WeylSpinor.left WeylSpinor.left)

def spinEquiv (p : Fin 4) : Representation.Equiv
    (BnvSevenFieldTensor.spinTensor (pattern p)) (spinCore p) := match p with
  | 0 => Representation.Equiv.refl _
  | 1 => DuqlOrderedCompleteness.spinSwap.symm
  | 2 => qddSpin
  | 3 => Representation.Equiv.refl _

def core (p : Fin 4) := external (gaugeCore p) (spinCore p)

def cover := BnvSevenGaugeTransport.cover.prodMap (MonoidHom.id WeylSpinor.Group)

theorem cover_surjective : Function.Surjective cover := by
  intro g
  obtain ⟨a, ha⟩ := BnvSevenGaugeTransport.cover_surjective g.1
  exact ⟨(a, g.2), by cases g; simp_all [cover]⟩

def corePullback (p : Fin 4) : Representation.Equiv
    (external ((gaugeCore p).comp BnvSevenGaugeTransport.cover) (spinCore p))
    ((core p).comp cover) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' g := by ext v w; rfl

def localEquiv (p : Fin 4) : Representation.Equiv
    (BnvSevenFieldTensor.localTensor (pattern p) (scalar p)) ((core p).comp cover) :=
  (BnvSevenFieldTensor.regroupLocal (pattern p) (scalar p)).trans
    ((externalEquiv (gaugeEquiv p) (spinEquiv p)).trans (corePullback p))

def invariantEquiv (p : Fin 4) : InvariantCoefficientTransport.Invariants
    (BnvSevenFieldTensor.localTensor (pattern p) (scalar p)) ≃ₗ[ℂ]
    InvariantCoefficientTransport.Invariants (core p) :=
  (InvariantCoefficientTransport.alongEquiv (localEquiv p)).trans
    (InvariantCoefficientTransport.alongSurjection (core p) cover cover_surjective)

abbrev Index : Fin 4 → Type
  | 0 => Fin 2 | 1 => Fin 2 | 2 => Fin 1 | 3 => Fin 2
instance (p : Fin 4) : Fintype (Index p) := match p with
  | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance | 3 => inferInstance
instance (p : Fin 4) : DecidableEq (Index p) := match p with
  | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance | 3 => inferInstance

def corePairing (p : Fin 4) : Index p → InvariantCoefficientTransport.Invariants (core p) :=
  match p with
  | 0 => BnvSevenLocal.pairing
  | 1 => BnvSevenLocal.mixedFourWeakPairing
  | 2 => fun _ => BnvSevenLocal.mixedPairing
  | 3 => BnvSevenLocal.pairing

def coreProbe (p : Fin 4) : Index p → GaugeCoreCarrier p ⊗[ℂ]
    ((WeylSpinor.Space ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ]
      (WeylSpinor.Space ⊗[ℂ] WeylSpinor.Space)) := match p with
  | 0 => BnvSevenLocal.probe
  | 1 => BnvSevenLocal.mixedFourWeakProbe
  | 2 => fun _ => BnvSevenLocal.mixedProbe
  | 3 => BnvSevenLocal.probe

theorem core_pairing_probe (p : Fin 4) (i j : Index p) :
    corePairing p i (coreProbe p j) = if i = j then 1 else 0 := by
  fin_cases p
  · exact BnvSevenLocal.pairing_probe i j
  · exact BnvSevenLocal.mixedFourWeak_pairing_probe i j
  · have h : i = j := Subsingleton.elim _ _
    rw [ite_eq_left h]
    exact BnvSevenLocal.mixed_normalized
  · exact BnvSevenLocal.pairing_probe i j

theorem core_reconstruction (p : Fin 4) (f : InvariantCoefficientTransport.Invariants (core p)) :
    f = ∑ i, f (coreProbe p i) • corePairing p i := by
  fin_cases p
  · exact BnvSevenLocal.reconstruction f
  · exact BnvSevenLocal.mixedFourWeak_reconstruction f
  · rw [Fin.sum_univ_one]
    exact BnvSevenLocal.mixed_unique f
  · exact BnvSevenLocal.reconstruction f

def pairing (p : Fin 4) (i : Index p) := (invariantEquiv p).symm (corePairing p i)
def probe (p : Fin 4) (i : Index p) := (localEquiv p).symm (coreProbe p i)

theorem pairing_probe (p : Fin 4) (i j : Index p) :
    pairing p i (probe p j) = if i = j then 1 else 0 := by
  change corePairing p i ((localEquiv p) ((localEquiv p).symm (coreProbe p j))) = _
  rw [Representation.Equiv.apply_symm_apply]
  exact core_pairing_probe p i j

theorem reconstruction (p : Fin 4) (f : InvariantCoefficientTransport.Invariants
    (BnvSevenFieldTensor.localTensor (pattern p) (scalar p))) :
    f = ∑ i, f (probe p i) • pairing p i := by
  apply (invariantEquiv p).injective
  rw [map_sum]
  simp only [map_smul]
  calc
    _ = ∑ i, ((invariantEquiv p) f) (coreProbe p i) • corePairing p i :=
      core_reconstruction p ((invariantEquiv p) f)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show invariantEquiv p (pairing p i) = corePairing p i from
        (invariantEquiv p).apply_symm_apply _]
      rfl

def flavorEquiv {R X : Type*} [Group R] [AddCommMonoid X] [Module ℂ X]
    (p : Fin 4) (x : Representation ℂ R X) :
    InvariantCoefficientTransport.Invariants
      (external (BnvSevenFieldTensor.localTensor (pattern p) (scalar p)) x) ≃ₗ[ℂ]
      (Index p → IntertwiningMap x (Representation.trivial ℂ R ℂ)) :=
  FiniteInvariantFactor.equiv _ x (pairing p) (probe p) (pairing_probe p) (reconstruction p)

/-- Compose local coordinates before specializing to large physical carriers. -/
def flavorAlongEquiv {R X B : Type*} [Group R]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid B] [Module ℂ B]
    (p : Fin 4) (x : Representation ℂ R X)
    (b : Representation ℂ ((StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) × R) B)
    (e : Representation.Equiv b
      (external (BnvSevenFieldTensor.localTensor (pattern p) (scalar p)) x)) :
    InvariantCoefficientTransport.Invariants b ≃ₗ[ℂ]
      (Index p → IntertwiningMap x (Representation.trivial ℂ R ℂ)) :=
  (InvariantCoefficientTransport.alongEquiv e).trans (flavorEquiv p x)

end
end GUT.BnvSevenLocalTransport
