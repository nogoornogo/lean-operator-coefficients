import Math.RepresentationTheory.Exterior.IndexedExteriorContent
import Physics.StandardModel.Operators.Support.Coordinates.SMChargedKernelRank
import Physics.StandardModel.Operators.Support.Coordinates.SMParityKernelRank

/-! The ten signed species dictionary connects the finite-tree decomposition
to every actual SM content, with arbitrary supplied residual flavor actions. -/
namespace Physics.SMIteratedContent
set_option autoImplicit false
noncomputable section
open Math Representation
open scoped TensorProduct

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

def counts : DeltaLOneSignedInput.Species → ℕ := fun s => (Finset.univ.filter (fun i => p i = s)).card

def leaves (c : DeltaLOneSignedInput.Species → ℕ) (s : DeltaLOneSignedInput.Species) :
    ExteriorContentTree.Leaf ((StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) × H) where
  Carrier := DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s
  rho := DeltaLOneSignedFields.field flavor s
  degree := c s

abbrev tree := IndexedExteriorContent.tree 9 (leaves flavor (counts p))
abbrev factor := ExteriorContentTree.factor (tree flavor p)
abbrev labelEquiv := IndexedExteriorContent.labels 9 (leaves flavor (counts p))
abbrev fieldEquiv := IndexedExteriorContent.fieldEquiv 9 (leaves flavor (counts p))

theorem degree_eq : ExteriorContentTree.degree (tree flavor p) = n :=
  IndexedExteriorContent.degree_of_counts 9 (leaves flavor (counts p)) p (fun _ => rfl)

/-- Full gauge, paired Weyl and residual actions are preserved at every degree. -/
def sourceEquiv : Representation.Equiv (factor flavor p) (SMContentWeakBound.source flavor p) :=
  IndexedExteriorContent.wordDecomposition 9 (leaves flavor (counts p)) p (fun _ => rfl)

local instance fieldFinite (s : DeltaLOneSignedInput.Species) : FiniteDimensional ℂ
    (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s) := by
  fin_cases s <;> dsimp [DeltaLOneSignedFields.Field,ThreeGenerationFermionBound.Flavor,
    DeltaLOneSignedFields.GaugeCarrier] <;> infer_instance

-- The field-dimension dictionary is definitionally the existing constant-
-- content dictionary. Keeping it here avoids importing a closed LLHH rank
-- certificate into the general mixed-character/decomposition interface.
def sourceDimension := ∏ s,
  ((![36,18,18,12,6,36,18,18,12,6] : DeltaLOneSignedInput.Species → ℕ) s).choose (counts p s)
def columns (m : ℕ) := sourceDimension p * (m+1)

theorem source_dimension : Module.finrank ℂ
    (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) p) = sourceDimension p := by
  have hd := IndexedExteriorContent.word_dimension 9 (leaves flavor (counts p)) p (fun _ => rfl)
    (fun s => fieldFinite s)
  change Module.finrank ℂ (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) p) = _ at hd
  rw [hd]
  apply Finset.prod_congr rfl
  intro s _
  change (Module.finrank ℂ (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s)).choose (counts p s) = _
  rw [ThreeGenerationFermionBound.species_dimension]

theorem carrier_dimension (m : ℕ) : Module.finrank ℂ (SMFullLocalKernel.Carrier flavor p m) = columns p m := by
  change Module.finrank ℂ (_ ⊗[ℂ] Sym[ℂ]^m WeakDoubletScalars.Doublet) = _
  rw [Module.finrank_tensorProduct,source_dimension,SymmetricPower.finrank_eq]
  simp [WeakDoubletScalars.Doublet,Nat.multichoose_two,columns]

theorem source_character (g : (StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) × H) :
    (SMContentWeakBound.source flavor p).character g =
      ∏ s, ((DeltaLOneSignedFields.field flavor s).exteriorPower (counts p s)).character g :=
  IndexedExteriorContent.word_character 9 (leaves flavor (counts p)) p (fun _ => rfl) (fun s => fieldFinite s) g

variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
  (b : Representation ℂ ((StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) × H) Y)

def withSpectator := ExternalInvariantTensor.tensorEquiv (sourceEquiv flavor p) (Representation.Equiv.refl b)

def coefficientEquiv : PatternCoefficientSupport.space (DeltaLOneSignedFields.field flavor) p b ≃ₗ[ℂ]
    InvariantCoefficientTransport.Invariants ((factor flavor p).tprod b) :=
  (PatternCoefficientSupport.equiv (DeltaLOneSignedFields.field flavor) p b).trans
    (InvariantCoefficientTransport.alongEquiv (withSpectator flavor p b)).symm

theorem rank_add_nullity (m : ℕ) (delta : ℤ) :
    Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints flavor p m delta)) +
      Module.finrank ℂ (SMFullLocalKernel.Kernel flavor p m delta) = columns p m := by
  have h := LinearMap.finrank_range_add_finrank_ker (SMFullLocalKernel.constraints flavor p m delta)
  simpa only [SMFullLocalKernel.Kernel,Module.finrank_fintype_fun_eq_card,Fintype.card_fin,
    carrier_dimension flavor p m] using h

theorem charged_rank (m : ℕ) (delta : ℤ) (hc : SMContentWeakBound.hypercharge p + 3*delta ≠ 0) :
    Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints flavor p m delta)) = columns p m := by
  simpa only [Fintype.card_fin,carrier_dimension flavor p m] using SMChargedKernelRank.full_rank flavor p m delta hc

theorem odd_rank (m : ℕ) (delta : ℤ) (hn : n % 2 ≠ 0) :
    Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints flavor p m delta)) = columns p m :=
  (SMParityKernelRank.full_rank flavor p m delta hn).trans (carrier_dimension flavor p m)

end
end Physics.SMIteratedContent
