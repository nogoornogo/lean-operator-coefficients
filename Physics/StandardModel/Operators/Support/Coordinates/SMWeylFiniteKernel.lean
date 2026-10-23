import Physics.StandardModel.Operators.Selection.QLFiniteSupport
import Physics.FieldTheory.Spinor.Weyl.WeylRealTransvections

/-! Actual arbitrary-content Weyl tests after exterior statistics and finite Higgs reduction. -/
namespace Physics.SMWeylFiniteKernel
set_option autoImplicit false
noncomputable section
open Math Representation AffineStatisticalSampling
open scoped TensorProduct
variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

def inclusion : WeylSpinor.Group →* NeutralHiggsPowers.G H where
  toFun g := ((1,g),1)
  map_one' := rfl
  map_mul' _ _ := by simp

def fieldDirection (s : DeltaLOneSignedInput.Species) (a : WeylRealTransvections.Index) :
    Module.End ℂ (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s) :=
  TensorProduct.map (TensorProduct.map LinearMap.id
    (WeylRealTransvections.direction (DeltaLOneSignedFields.rightHanded s) a)) LinearMap.id

theorem field_affine (s : DeltaLOneSignedInput.Species) (a : WeylRealTransvections.Index)
    (t : ℝ) (x : DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s) :
    DeltaLOneSignedFields.field flavor s (inclusion (WeylRealTransvections.family a t)) x =
      x + (t : ℂ) • fieldDirection s a x := by
  have he : DeltaLOneSignedFields.field flavor s (inclusion (WeylRealTransvections.family a t)) =
      LinearMap.id + (t : ℂ) • fieldDirection s a := by
    ext u v w
    simp [DeltaLOneSignedFields.field, DeltaLOneSignedFields.localField,
      ExternalInvariantTensor.external, inclusion, Representation.tprod_apply,
      WeylRealTransvections.spinor_affine, fieldDirection, TensorProduct.tmul_add,
      TensorProduct.tmul_smul, TensorProduct.add_tmul, TensorProduct.smul_tmul']
  exact LinearMap.congr_fun he x

variable {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

def source := (SMContentWeakBound.source flavor p).comp (inclusion (H := H))

theorem source_polynomial (a : WeylRealTransvections.Index) :
    PolynomialOrbits (WeylRealTransvections.family a) (source flavor p) n := by
  have hp := statistical_source (fun t => inclusion (H := H) (WeylRealTransvections.family a t))
    (DeltaLOneSignedFields.field flavor) p
    (fun i x => ⟨fieldDirection (p i) a x, fun t => field_affine flavor (p i) a t x⟩)
  exact hp

abbrev fullAction (m : ℕ) (delta : ℤ) :=
  (SMFiniteHiggsSupport.source flavor p).tprod
    (BoundedHiggsSupport.constituent (SMHiggsConstituents.weakProjection (H := H))
      SMHiggsConstituents.character m delta)
def action (m : ℕ) (delta : ℤ) := (fullAction flavor p m delta).comp (inclusion (H := H))

theorem boson_fixed (m : ℕ) (delta : ℤ) (g : WeylSpinor.Group)
    (x : Sym[ℂ]^m WeakDoubletScalars.Doublet) :
    BoundedHiggsSupport.constituent (SMHiggsConstituents.weakProjection (H := H))
      SMHiggsConstituents.character m delta (inclusion g) x = x := by
  have hc : SMHiggsConstituents.character (inclusion (H := H) g) = 1 := by
    apply Units.ext
    simp [SMHiggsConstituents.character_apply, inclusion, StandardSMGaugeTensor.phase]
  change ((SMHiggsConstituents.character^delta) (inclusion g) : ℂˣ) •
    (WeakDoubletScalars.doublet.symmetricPower m) 1 x = x
  simp [hc]

theorem action_polynomial (m : ℕ) (delta : ℤ) (a : WeylRealTransvections.Index) :
    PolynomialOrbits (WeylRealTransvections.family a) (action flavor p m delta) n :=
  tensor_fixed (WeylRealTransvections.family a) (source flavor p)
    ((BoundedHiggsSupport.constituent (SMHiggsConstituents.weakProjection (H := H))
      SMHiggsConstituents.character m delta).comp (inclusion (H := H))) n
    (source_polynomial flavor p a) (fun _t x => boson_fixed m delta _ x)

theorem exhaustive (m : ℕ) (delta : ℤ) :
    FiniteInvariantKernel.Exhaustive (action flavor p m delta) (WeylRealTransvections.tests n) :=
  WeylRealTransvections.exhaustive (action flavor p m delta) n (action_polynomial flavor p m delta)

variable {J : Type*} [Fintype J] [DecidableEq J]
  (m : ℕ) (delta : ℤ)
  (b : Module.Basis J ℂ ((PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) p)
    ⊗[ℂ] Sym[ℂ]^m WeakDoubletScalars.Doublet))

def coefficientEquiv :
    InvariantCoefficientTransport.Invariants (action flavor p m delta) ≃ₗ[ℂ]
      FiniteInvariantKernel.Kernel (action flavor p m delta) b (WeylRealTransvections.tests n) :=
  FiniteInvariantKernel.equiv _ b _ (exhaustive flavor p m delta)

theorem allowed_iff_rank_lt :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (action flavor p m delta)) ↔
      Module.finrank ℂ (LinearMap.range (FiniteInvariantKernel.constraints
        (action flavor p m delta) b (WeylRealTransvections.tests n))) < Fintype.card J :=
  FiniteInvariantKernel.allowed_iff_rank_lt _ b _ (exhaustive flavor p m delta)

local instance fieldFinite (s : DeltaLOneSignedInput.Species) :
    FiniteDimensional ℂ (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s) := by
  fin_cases s <;> dsimp [DeltaLOneSignedFields.Field, ThreeGenerationFermionBound.Flavor,
    DeltaLOneSignedFields.GaugeCarrier] <;> infer_instance

local instance sourceFinite :
    FiniteDimensional ℂ (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) p) := by
  change FiniteDimensional ℂ (LinearMap.range (PatternExteriorSource.map
    (DeltaLOneSignedFields.field flavor) p).toLinearMap)
  infer_instance

abbrev Carrier := (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) p)
  ⊗[ℂ] Sym[ℂ]^m WeakDoubletScalars.Doublet

def basis : Module.Basis (Fin (Module.finrank ℂ (Carrier flavor p m))) ℂ (Carrier flavor p m) :=
  Module.finBasis ℂ (Carrier flavor p m)

/-- Canonical finite coordinates for the actual statistical carrier; basis choice is classical. -/
def canonicalEquiv : InvariantCoefficientTransport.Invariants (action flavor p m delta) ≃ₗ[ℂ]
    FiniteInvariantKernel.Kernel (action flavor p m delta) (basis flavor p m)
      (WeylRealTransvections.tests n) := coefficientEquiv flavor p m delta (basis flavor p m)

end
end Physics.SMWeylFiniteKernel
