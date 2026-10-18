import Physics.StandardModel.Operators.CyclicResidualSelection
import Physics.StandardModel.Operators.QqueSpinorExterior
import Physics.StandardModel.Operators.FlavoredCyclicCoordinates

/-! Bounded model controls on explicitly supplied broken-phase dictionaries.
No UV branching, mass classification, VEV stabilizer or matching is assumed proved. -/
namespace GUT.ProtonProtectionModelControls
set_option autoImplicit false
noncomputable section
universe u
open Math Representation CyclicResidualSelection SelectionCriteria

/-- Pure baryonic subgroup of the product-cover B/L model, using b = 6B. -/
def baryonCharges : Charges 18 := ![2,2,2,0,0]

theorem baryon_families_nonzero (i : Fin 4) :
    familyCharge baryonCharges i ≠ 0 := by
  fin_cases i <;> decide +kernel

/-- Conditional on the supplied dictionary: all four physical families vanish. -/
theorem baryon_selection :
    Forbidden (DeltaLOneSignedFields.Sector (flavor baryonCharges) 1) :=
  (forbidden_total_iff _).mpr baryon_families_nonzero

/-- Uniform baryon charges forbid physical qque for arbitrary finite
flavor index sets, not only the single-generation control above. -/
theorem baryon_qque_all_flavors
    (I J K : Type u) [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K] :
    Forbidden (QquePhysicalExteriorCompleteness.Sector
      (CyclicWeightCoordinates.diagonal (fun _ : I => (2 : ZMod 18)))
      (CyclicWeightCoordinates.diagonal (fun _ : J => (2 : ZMod 18)))
      (CyclicWeightCoordinates.diagonal (fun _ : K => (0 : ZMod 18)))) :=
  (FlavoredCyclicCoordinates.qque_forbidden
    (fun _ : I => (2 : ZMod 18)) (fun _ : J => (2 : ZMod 18))
    (fun _ : K => (0 : ZMod 18))).mpr (by
  intro i
  have hc : FlavoredCyclicCoordinates.qqueCharge
      (fun _ : I => (2 : ZMod 18)) (fun _ : J => (2 : ZMod 18))
      (fun _ : K => (0 : ZMod 18)) i = 6 := by
    simp [FlavoredCyclicCoordinates.qqueCharge,
      CyclicWeightCoordinates.symmetricCharge, Sym.card_coe]
    norm_num
  rw [hc]
  decide +kernel)

/-- Light lepton parity only; this is not a symmetry of the full split SU5 mass. -/
def lightLeptonParity : Charges 2 := ![0,0,0,1,1]

theorem light_parity_families_nonzero (i : Fin 4) :
    familyCharge lightLeptonParity i ≠ 0 := by
  fin_cases i <;> decide +kernel

theorem light_parity_selection :
    Forbidden (DeltaLOneSignedFields.Sector (flavor lightLeptonParity) 1) :=
  (forbidden_total_iff _).mpr light_parity_families_nonzero

/-- The gauge-only broken-phase PS dictionary has no extra residual charge. -/
def gaugeOnlyCharges : Charges 1 := 0

theorem gauge_only_qque_allowed :
    Allowed (DeltaLOneFourFamilyDecomposition.FamilySector (flavor gaugeOnlyCharges) 1) := by
  apply (allowed_family_iff _ _).mpr
  exact Subsingleton.elim _ _

section ScalarEmbeddings
variable {K S V W : Type*} [Field K]
  [AddCommGroup S] [Module K S]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Two injective full-copy embeddings force equal scalar actions at any
one residual element. The source action need not have been assumed scalar. -/
theorem equal_scalars_of_common_embeddings [Nontrivial S]
    (A : S →ₗ[K] S) (f : S →ₗ[K] V) (g : S →ₗ[K] W)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (a b : K) (ha : ∀ x, f (A x) = a • f x)
    (hb : ∀ x, g (A x) = b • g x) : a = b := by
  obtain ⟨x,hx⟩ := exists_ne (0 : S)
  have hA : A x = a • x := hf (by simpa using ha x)
  have hB : A x = b • x := hg (by simpa using hb x)
  have he : (a-b) • x = 0 := by rw [sub_smul, ← hA, ← hB, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp he).resolve_right hx)

end ScalarEmbeddings
end
end GUT.ProtonProtectionModelControls
