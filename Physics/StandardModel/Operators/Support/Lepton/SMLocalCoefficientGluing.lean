import Math.RepresentationTheory.Coefficients.InvariantCoefficientGluing
import Math.RepresentationTheory.SU2.TwistedSU2ConstituentCoupling
import Math.RepresentationTheory.Exterior.BinaryPatternExterior
import Math.RepresentationTheory.Exterior.ConstantPatternExterior
import Physics.StandardModel.Operators.Support.Coordinates.SMIntegralLocalWeights

/-! Actual gluing for two distinct constant-species statistical blocks.
The source equivalence requires distinct species: multiplying overlapping
fermion blocks is not assumed to preserve nonzeroness. -/
namespace Physics.SMLocalCoefficientGluing
set_option autoImplicit false
noncomputable section
open Math Representation
open scoped TensorProduct

@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

abbrev weakProjection : SMIntegralLocalWeights.Group →* TauCeti.SU2 :=
  (SMHiggsConstituents.weakProjection (H := H)).comp (MonoidHom.inl _ _)
abbrev character : SMIntegralLocalWeights.Group →* ℂˣ :=
  (SMHiggsConstituents.character (H := H)).comp (MonoidHom.inl _ _)
abbrev boson (m : ℕ) (delta : ℤ) :=
  BoundedHiggsSupport.constituent (weakProjection (H := H)) (character (H := H)) m delta

def bosonEquiv (m : ℕ) (delta : ℤ) : Representation.Equiv
    (SMIntegralLocalWeights.boson (H := H) m delta) (boson (H := H) m delta) where
  toLinearEquiv := .refl ℂ _
  isIntertwining' _ := rfl

local instance bosonIrreducible (m : ℕ) (delta : ℤ) : IsIrreducible (boson (H := H) m delta) := by
  apply (Representation.isIrreducible_charTwist_iff _ _).mpr
  have hi : IsIrreducible ((((WeakDoubletScalars.doublet.symmetricPower m).comp
      (weakProjection (H := H))).comp SMIntegralLocalWeights.weak)) := by
    change IsIrreducible (WeakDoubletScalars.doublet.symmetricPower m)
    infer_instance
  exact RepresentationTheory.isIrreducible_of_comp _ SMIntegralLocalWeights.weak

local instance bosonDualIrreducible (m : ℕ) (delta : ℤ) :
    IsIrreducible (boson (H := H) m delta).dual :=
  RepresentationTheory.dual_isIrreducible _

def fullSourceEquiv (s t : DeltaLOneSignedInput.Species) (n m : ℕ) (hst : s≠t) :
    Representation.Equiv
      ((SMContentWeakBound.source flavor (fun _ : Fin n => s)).tprod
        (SMContentWeakBound.source flavor (fun _ : Fin m => t)))
      (SMContentWeakBound.source flavor (BinaryPatternExterior.pattern s t n m)) := by
  let e := ExternalInvariantTensor.tensorEquiv
      (ConstantPatternExterior.equiv (DeltaLOneSignedFields.field flavor) s n).symm
      (ConstantPatternExterior.equiv (DeltaLOneSignedFields.field flavor) t m).symm
  exact e.trans (BinaryPatternExterior.equiv (DeltaLOneSignedFields.field flavor) s t n m hst)

def sourceEquiv (s t : DeltaLOneSignedInput.Species) (n m : ℕ) (hst : s≠t) :
    Representation.Equiv
      ((SMIntegralLocalWeights.source flavor (fun _ : Fin n => s)).tprod
        (SMIntegralLocalWeights.source flavor (fun _ : Fin m => t)))
      (SMIntegralLocalWeights.source flavor (BinaryPatternExterior.pattern s t n m)) where
  toLinearEquiv := (fullSourceEquiv flavor s t n m hst).toLinearEquiv
  isIntertwining' g := (fullSourceEquiv flavor s t n m hst).isIntertwining' (g,1)

theorem allowed (s t : DeltaLOneSignedInput.Species) (n m x y : ℕ) (hst : s≠t)
    (r : SU2ClebschGordan.Index x y) (delta epsilon : ℤ)
    (hf : SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (fun _ : Fin n => s) x delta)))
    (hg : SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (fun _ : Fin m => t) y epsilon))) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (BinaryPatternExterior.pattern s t n m)
        (SU2ClebschGordan.degree x y r) (delta+epsilon))) := by
  let a := SMIntegralLocalWeights.source flavor (fun _ : Fin n => s)
  let d := SMIntegralLocalWeights.source flavor (fun _ : Fin m => t)
  have hf' := (SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv
    (ExternalInvariantTensor.tensorEquiv (.refl a) (bosonEquiv (H := H) x delta)))).mp hf
  have hg' := (SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv
    (ExternalInvariantTensor.tensorEquiv (.refl d) (bosonEquiv (H := H) y epsilon)))).mp hg
  let tmodel := boson (H := H) (SU2ClebschGordan.degree x y r) (delta+epsilon)
  let : Nontrivial (Sym[ℂ]^(SU2ClebschGordan.degree x y r) WeakDoubletScalars.Doublet) :=
    IsIrreducible.nontrivial (ρ := tmodel) inferInstance
  have ht := InvariantCoefficientGluing.allowed a d (boson (H := H) x delta)
    (boson (H := H) y epsilon) tmodel hf' hg'
    (TwistedSU2ConstituentCoupling.embed (weakProjection (H := H)) (character (H := H)) x y r delta epsilon)
    (TwistedSU2ConstituentCoupling.embed_injective _ _ x y r delta epsilon)
  exact (SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv
    (ExternalInvariantTensor.tensorEquiv (sourceEquiv flavor s t n m hst)
      (bosonEquiv (H := H) _ (delta+epsilon)).symm))).mp ht

/-- Transport labels before specializing the large statistical carrier. -/
theorem allowed_at (s t : DeltaLOneSignedInput.Species) (n m x y : ℕ) (hst : s≠t)
    (r : SU2ClebschGordan.Index x y) (delta epsilon : ℤ) (u : ℕ) (z : ℤ)
    (hu : SU2ClebschGordan.degree x y r=u) (hz : delta+epsilon=z)
    (hf : SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (fun _ : Fin n => s) x delta)))
    (hg : SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (fun _ : Fin m => t) y epsilon))) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (BinaryPatternExterior.pattern s t n m) u z)) := by
  subst u
  subst z
  exact allowed flavor s t n m x y hst r delta epsilon hf hg

end
end Physics.SMLocalCoefficientGluing
