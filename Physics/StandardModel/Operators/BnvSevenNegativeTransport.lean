import Physics.StandardModel.Operators.BnvLocalConjugation
import Physics.StandardModel.Operators.BnvSevenLocalTransport

open Math

/-! Negative dimension-seven local tensors transported through an involutive
group automorphism, without identifying opposite flavor multiplicities. -/
namespace GUT.BnvSevenNegativeTransport
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor

def pattern : Fin 4 → Fin 4 → DeltaLOneSignedInput.Species :=
  ![![6,7,7,3], ![5,5,7,3], ![5,7,7,4], ![7,7,7,3]]
def scalar : Fin 4 → BnvMixedInput.ScalarSpecies := ![0,0,0,1]

def restrictEquiv {G H A B : Type*} [Group G] [Group H]
    [AddCommMonoid A] [Module ℂ A] [AddCommMonoid B] [Module ℂ B]
    {a : Representation ℂ H A} {b : Representation ℂ H B}
    (e : Representation.Equiv a b) (f : G →* H) :
    Representation.Equiv (a.comp f) (b.comp f) where
  toLinearEquiv := e.toLinearEquiv
  isIntertwining' g := e.isIntertwining' (f g)

def relabel {a b : Fin 4 → DeltaLOneSignedInput.Species}
    {u v : BnvMixedInput.ScalarSpecies} (h : a = b) (k : u = v) :
    Representation.Equiv (BnvSevenFieldTensor.localTensor a u)
      (BnvSevenFieldTensor.localTensor b v) := by
  subst b
  subst v
  exact Representation.Equiv.refl _

theorem opposite_pattern (p : Fin 4) :
    BnvLocalConjugation.opposite ∘ pattern p = BnvSevenPatternDescent.pattern p := by
  funext i
  fin_cases p <;> fin_cases i <;> rfl

theorem opposite_scalar (p : Fin 4) :
    BnvLocalConjugation.oppositeScalar (scalar p) = BnvSevenPatternDescent.scalar p := by
  fin_cases p <;> rfl

def positive (p : Fin 4) := (BnvLocalConjugation.five (pattern p) (scalar p)).trans
  (restrictEquiv (relabel (opposite_pattern p) (opposite_scalar p))
    BnvLocalConjugation.conjugate)

def localEquiv (p : Fin 4) := (positive p).trans
  (restrictEquiv (BnvSevenLocalTransport.localEquiv p) BnvLocalConjugation.conjugate)

def invariantEquiv (p : Fin 4) :=
  (InvariantCoefficientTransport.alongEquiv (positive p)).trans
    (InvariantCoefficientTransport.alongSurjection
      (BnvSevenFieldTensor.localTensor (BnvSevenPatternDescent.pattern p)
        (BnvSevenPatternDescent.scalar p))
      BnvLocalConjugation.conjugate BnvLocalConjugation.surjective)

abbrev Index := BnvSevenLocalTransport.Index

def pairing (p : Fin 4) (i : Index p) :=
  (invariantEquiv p).symm (BnvSevenLocalTransport.pairing p i)

def probe (p : Fin 4) (i : Index p) :=
  (positive p).symm (BnvSevenLocalTransport.probe p i)

theorem pairing_probe (p : Fin 4) (i j : Index p) :
    pairing p i (probe p j) = if i = j then 1 else 0 := by
  change BnvSevenLocalTransport.pairing p i
    ((positive p) ((positive p).symm (BnvSevenLocalTransport.probe p j))) = _
  rw [Representation.Equiv.apply_symm_apply]
  exact BnvSevenLocalTransport.pairing_probe p i j

theorem reconstruction (p : Fin 4) (f : InvariantCoefficientTransport.Invariants
    (BnvSevenFieldTensor.localTensor (pattern p) (scalar p))) :
    f = ∑ i, f (probe p i) • pairing p i := by
  apply (invariantEquiv p).injective
  rw [map_sum]
  simp only [map_smul]
  calc
    _ = ∑ i, ((invariantEquiv p) f) (BnvSevenLocalTransport.probe p i) •
        BnvSevenLocalTransport.pairing p i :=
      BnvSevenLocalTransport.reconstruction p ((invariantEquiv p) f)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show invariantEquiv p (pairing p i) = BnvSevenLocalTransport.pairing p i from
        (invariantEquiv p).apply_symm_apply _]
      rfl

def flavorEquiv {R X : Type*} [Group R] [AddCommMonoid X] [Module ℂ X]
    (p : Fin 4) (x : Representation ℂ R X) :
    InvariantCoefficientTransport.Invariants
      (external (BnvSevenFieldTensor.localTensor (pattern p) (scalar p)) x) ≃ₗ[ℂ]
      (Index p → IntertwiningMap x (Representation.trivial ℂ R ℂ)) :=
  FiniteInvariantFactor.equiv _ x (pairing p) (probe p) (pairing_probe p) (reconstruction p)

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
end GUT.BnvSevenNegativeTransport
