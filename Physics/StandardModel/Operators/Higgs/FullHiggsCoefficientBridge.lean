import Math.RepresentationTheory.Coefficients.TwoSpeciesCoefficientBridge
import Physics.StandardModel.Operators.Higgs.HiggsPatternDescent
import Physics.StandardModel.Operators.Support.Coordinates.SMHiggsConstituents
import Physics.StandardModel.Operators.Higgs.WeakSingletHiggsSupport

/-! Original full-field fixed Higgs content connected to the actual SM constituents. -/
namespace Physics.FullHiggsCoefficientBridge
set_option autoImplicit false
noncomputable section
open Math Representation BnvMixedInput DeltaLOneSignedFields
open scoped TensorProduct
variable {H : Type*} [Group H]

def leftEquiv : Representation.Equiv (scalarField (NeutralHiggsPowers.flavor (H := H)) 0)
    (NeutralHiggsPowers.higgs (H := H)) :=
  ExternalUnitEquivalence.equiv (H := H)
    ((scalarGauge 0).comp (MonoidHom.fst StandardSMGaugeTensor.GaugeGroup WeylSpinor.Group))

def rightEquiv : Representation.Equiv (scalarField (NeutralHiggsPowers.flavor (H := H)) 1)
    (NeutralHiggsPowers.higgs (H := H)).dual :=
  ExternalUnitEquivalence.equiv (H := H)
    ((scalarGauge 1).comp (MonoidHom.fst StandardSMGaugeTensor.GaugeGroup WeylSpinor.Group))

def bosonsEquiv (h d : ℕ) : Representation.Equiv
    (TwoSpeciesCoefficientBridge.Split (scalarField (NeutralHiggsPowers.flavor (H := H))) h d)
    (SMHiggsConstituents.Bosons (H := H) h d) :=
  ExternalInvariantTensor.tensorEquiv (leftEquiv.symmetricPower h) (rightEquiv.symmetricPower d)

variable {X : Type*} [AddCommGroup X] [Module ℂ X]
  (a : Representation ℂ (NeutralHiggsPowers.G H) X)

abbrev Space (h d : ℕ) := TypedSymmetricPatternHom.sourceSpace
  (scalarField (NeutralHiggsPowers.flavor (H := H))) (TwoSpeciesPattern.pattern h d) a

theorem mem_space_iff (h d : ℕ)
    (f : InvariantCoefficientTransport.Invariants
      (a.tprod ((FiniteSpeciesExterior.representation
        (scalarField (NeutralHiggsPowers.flavor (H := H)))).symmetricPower (h+d)))) :
    f ∈ Space a h d ↔
      ∀ labels : Fin (h+d) → ScalarSpecies,
        ((Finset.univ.filter (fun i => labels i = 0)).card ≠ h ∨
          (Finset.univ.filter (fun i => labels i = 1)).card ≠ d) →
        ∀ (v : ∀ i, ScalarField (S := NeutralHiggsPowers.Multiplicity) (labels i)) (x : X),
          f (x ⊗ₜ[ℂ] SymmetricPower.tprod ℂ (fun i => Pi.single (labels i) (v i))) = 0 := by
  rw [TypedSymmetricPatternHom.sourceSpace_iff]
  simp_rw [TwoSpeciesPattern.orbit_iff_counts,not_and_or]

def splitEquiv (h d : ℕ) : Space a h d ≃ₗ[ℂ]
    InvariantCoefficientTransport.Invariants (a.tprod (SMHiggsConstituents.Bosons (H := H) h d)) :=
  (TwoSpeciesCoefficientBridge.sourceEquiv _ a h d).trans
    (InvariantCoefficientTransport.alongEquiv
      (ExternalInvariantTensor.tensorEquiv (.refl a) (bosonsEquiv h d)))

def constituentEquiv (h d : ℕ) : Space a h d ≃ₗ[ℂ]
    InvariantCoefficientTransport.Invariants
      (a.tprod (FiniteBlockHom.action (TwistedSU2ClebschGordan.summand
        (SMHiggsConstituents.weakProjection (H := H)) SMHiggsConstituents.character h d))) :=
  (splitEquiv a h d).trans (InvariantCoefficientTransport.alongEquiv
    (ExternalInvariantTensor.tensorEquiv (.refl a) (SMHiggsConstituents.equivalence h d)))

theorem allowed_iff (h d : ℕ) : SelectionCriteria.Allowed (Space a h d) ↔
    SelectionCriteria.Allowed
      (InvariantCoefficientTransport.Invariants
        (a.tprod (FiniteBlockHom.action (TwistedSU2ClebschGordan.summand
          (SMHiggsConstituents.weakProjection (H := H)) SMHiggsConstituents.character h d)))) :=
  SelectionCriteria.allowed_equiv (constituentEquiv a h d)

theorem forbidden_iff (h d : ℕ) : SelectionCriteria.Forbidden (Space a h d) ↔
    SelectionCriteria.Forbidden
      (InvariantCoefficientTransport.Invariants
        (a.tprod (FiniteBlockHom.action (TwistedSU2ClebschGordan.summand
          (SMHiggsConstituents.weakProjection (H := H)) SMHiggsConstituents.character h d)))) :=
  (SelectionCriteria.ofEquiv (constituentEquiv a h d)).forbidden

theorem weakSinglet_allowed_iff
    (ha : ∀ u x, a (WeakSingletHiggsSupport.weakInclusion u) x = x) (h d : ℕ) :
    SelectionCriteria.Allowed (Space a h d) ↔
      h=d ∧ SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants a) :=
  (SelectionCriteria.allowed_equiv (splitEquiv a h d)).trans
    (WeakSingletHiggsSupport.allowed_iff a ha h d)

section Matter
variable {F : DeltaLOneSignedInput.Species → Type*}
  [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  (flavor : ∀ s, Representation ℂ H (F s)) (n : ℕ)

def matterEquiv (h d : ℕ) :
    HiggsPatternDescent.Space flavor n (TwoSpeciesPattern.pattern h d) ≃ₗ[ℂ]
      InvariantCoefficientTransport.Invariants
        ((HiggsPatternDescent.source flavor n).tprod
          (FiniteBlockHom.action (TwistedSU2ClebschGordan.summand
            (SMHiggsConstituents.weakProjection (H := H)) SMHiggsConstituents.character h d))) :=
  constituentEquiv (HiggsPatternDescent.source flavor n) h d
end Matter

end
end Physics.FullHiggsCoefficientBridge
