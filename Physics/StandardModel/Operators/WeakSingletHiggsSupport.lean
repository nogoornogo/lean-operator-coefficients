import Math.RepresentationTheory.WeakSingletHiggsReduction
import Math.RepresentationTheory.Decomposition.ScalarIrreducible
import Physics.StandardModel.Operators.NeutralHiggsPowers

/-! Actual SM weak-doublet reduction for weak-singlet matter. The fermion
source retains color, Weyl and residual invariance and its exterior statistics. -/
namespace GUT.WeakSingletHiggsSupport
set_option autoImplicit false
noncomputable section
open Math Representation StandardSMGaugeTensor DeltaLOneSignedFields
open scoped TensorProduct
variable {H : Type*} [Group H]

def weakInclusion : WeakDoubletScalars.Group →* NeutralHiggsPowers.G H where
  toFun u := (((1,(u,1)),1),1)
  map_one' := rfl
  map_mul' _ _ := by simp

theorem higgs_weak (u : WeakDoubletScalars.Group) (v : WeakDoubletScalars.Doublet) :
    NeutralHiggsPowers.higgs (weakInclusion (H := H) u) v = WeakDoubletScalars.doublet u v := by
  change phase 3 (1,(u,1)) • Matrix.toLin' (u : Matrix (Fin 2) (Fin 2) ℂ) v =
    (u : Matrix (Fin 2) (Fin 2) ℂ).mulVec v
  have hp : phase 3 (1,(u,1)) = 1 := by simp [phase]
  rw [hp,one_smul]
  rfl

variable {X : Type*} [AddCommGroup X] [Module ℂ X]
  (a : Representation ℂ (NeutralHiggsPowers.G H) X)

abbrev Space (h d : ℕ) :=
  WeakSingletHiggsReduction.Coefficients a (NeutralHiggsPowers.higgs (H := H)) h d

def equiv (ha : ∀ u x, a (weakInclusion u) x = x) (m : ℕ) :
    Space a m m ≃ₗ[ℂ] InvariantCoefficientTransport.Invariants a :=
  WeakSingletHiggsReduction.equiv a NeutralHiggsPowers.higgs weakInclusion higgs_weak ha m

theorem allowed_iff (ha : ∀ u x, a (weakInclusion u) x = x) (h d : ℕ) :
    SelectionCriteria.Allowed (Space a h d) ↔
      h=d ∧ SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants a) :=
  WeakSingletHiggsReduction.allowed_iff a NeutralHiggsPowers.higgs weakInclusion higgs_weak ha h d

theorem forbidden_iff (ha : ∀ u x, a (weakInclusion u) x = x) (h d : ℕ) :
    SelectionCriteria.Forbidden (Space a h d) ↔
      h≠d ∨ SelectionCriteria.Forbidden (InvariantCoefficientTransport.Invariants a) :=
  WeakSingletHiggsReduction.forbidden_iff a NeutralHiggsPowers.higgs weakInclusion higgs_weak ha h d

theorem all_forbidden_iff (ha : ∀ u x, a (weakInclusion u) x = x) :
    (∀ h d, SelectionCriteria.Forbidden (Space a h d)) ↔
      SelectionCriteria.Forbidden (InvariantCoefficientTransport.Invariants a) :=
  WeakSingletHiggsReduction.all_forbidden_iff a NeutralHiggsPowers.higgs weakInclusion higgs_weak ha

def scalarEquiv (m : ℕ) : Space (trivial ℂ (NeutralHiggsPowers.G H) ℂ) m m ≃ₗ[ℂ] ℂ :=
  (equiv (trivial ℂ (NeutralHiggsPowers.G H) ℂ) (by intro u x; rfl) m).trans
    (by
      letI := ScalarIrreducible.irreducible (trivial ℂ (NeutralHiggsPowers.G H) ℂ)
      exact (IrreducibleHomScalar.equiv _ _ (Representation.Equiv.refl _)).symm)

def singletSpecies : Fin 6 → DeltaLOneSignedInput.Species := ![1,2,4,6,7,9]

private theorem color_weak (w : ℤ) (u : WeakDoubletScalars.Group) (v : SMEpsilonTensor.Color) :
    twist color w (1,(u,1)) v = v := by
  change phase w (1,(u,1)) • Matrix.toLin' (1 : Matrix (Fin 3) (Fin 3) ℂ) v = v
  have hp : phase w (1,(u,1)) = 1 := by simp [phase]
  rw [hp,one_smul,Matrix.toLin'_one]
  rfl

private theorem electron_weak (u : WeakDoubletScalars.Group) (v : ℂ) :
    electronRight (1,(u,1)) v = v := by
  change phase (-6) (1,(u,1)) • v = v
  have hp : phase (-6) (1,(u,1)) = 1 := by simp [phase]
  rw [hp,one_smul]

theorem singlet_gauge_weak (i : Fin 6) (u : WeakDoubletScalars.Group)
    (v : GaugeCarrier (singletSpecies i)) : gauge (singletSpecies i) (1,(u,1)) v = v := by
  fin_cases i
  · exact color_weak 4 u v
  · exact color_weak (-2) u v
  · exact electron_weak u v
  · change Module.Dual ℂ SMEpsilonTensor.Color at v
    apply LinearMap.ext
    intro x
    change v (twist color 4 ((1,(u,1)) : GaugeGroup)⁻¹ x) = v x
    rw [show ((1,(u,1)) : GaugeGroup)⁻¹ = (1,(u⁻¹,1)) from by simp,color_weak]
  · change Module.Dual ℂ SMEpsilonTensor.Color at v
    apply LinearMap.ext
    intro x
    change v (twist color (-2) ((1,(u,1)) : GaugeGroup)⁻¹ x) = v x
    rw [show ((1,(u,1)) : GaugeGroup)⁻¹ = (1,(u⁻¹,1)) from by simp,color_weak]
  · change Module.Dual ℂ ℂ at v
    apply LinearMap.ext
    intro x
    change v (electronRight ((1,(u,1)) : GaugeGroup)⁻¹ x) = v x
    rw [show ((1,(u,1)) : GaugeGroup)⁻¹ = (1,(u⁻¹,1)) from by simp,electron_weak]

variable {F : DeltaLOneSignedInput.Species → Type*}
  [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  (flavor : ∀ s, Representation ℂ H (F s))

def matter := FiniteSpeciesExterior.representation (fun i : Fin 6 => field flavor (singletSpecies i))

theorem singlet_field_weak (i : Fin 6) (u : WeakDoubletScalars.Group)
    (v : Field (F := F) (singletSpecies i)) : field flavor (singletSpecies i) (weakInclusion u) v = v := by
  have he : field flavor (singletSpecies i) (weakInclusion u) = LinearMap.id := by
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro z
    change (gauge (singletSpecies i) (1,(u,1)) x ⊗ₜ[ℂ]
      FourSameWeylCompleteness.action (rightHanded (singletSpecies i)) 1 y) ⊗ₜ[ℂ]
      flavor (singletSpecies i) 1 z = (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z
    rw [singlet_gauge_weak]
    simp
  exact DFunLike.congr_fun he v

theorem matter_weak (u : WeakDoubletScalars.Group)
    (v : ∀ i : Fin 6, Field (F := F) (singletSpecies i)) :
    matter flavor (weakInclusion u) v = v := by
  funext i
  exact singlet_field_weak flavor i u (v i)

theorem exterior_weak (n : ℕ) (u : WeakDoubletScalars.Group)
    (v : ⋀[ℂ]^n (∀ i : Fin 6, Field (F := F) (singletSpecies i))) :
    (matter flavor).exteriorPower n (weakInclusion u) v = v := by
  have he : (matter flavor).exteriorPower n (weakInclusion u) = LinearMap.id := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro vv
    change (matter flavor).exteriorPower n (weakInclusion u) (exteriorPower.ιMulti ℂ n vv) =
      exteriorPower.ιMulti ℂ n vv
    rw [Representation.exteriorPower_apply_ιMulti]
    change exteriorPower.ιMulti ℂ n (fun i => matter flavor (weakInclusion u) (vv i)) =
      exteriorPower.ιMulti ℂ n vv
    congr 1
    funext i
    exact matter_weak flavor u (vv i)
  exact DFunLike.congr_fun he v

/-- All exterior degrees of the actual uR,dR,eR and signed dual field sum. -/
def matterEquiv (n m : ℕ) : Space ((matter flavor).exteriorPower n) m m ≃ₗ[ℂ]
    InvariantCoefficientTransport.Invariants ((matter flavor).exteriorPower n) :=
  equiv ((matter flavor).exteriorPower n) (exterior_weak flavor n) m

theorem matter_allowed_iff (n h d : ℕ) :
    SelectionCriteria.Allowed (Space ((matter flavor).exteriorPower n) h d) ↔
      h=d ∧ SelectionCriteria.Allowed
        (InvariantCoefficientTransport.Invariants ((matter flavor).exteriorPower n)) :=
  allowed_iff ((matter flavor).exteriorPower n) (exterior_weak flavor n) h d

def matterZeroDegreeReduction (n m : ℕ) :
    Space ((matter flavor).exteriorPower n) m m ≃ₗ[ℂ]
      Space ((matter flavor).exteriorPower n) 0 0 :=
  (matterEquiv flavor n m).trans (matterEquiv flavor n 0).symm

theorem all_matter_forbidden_zero_iff (n : ℕ) :
    (∀ h d, SelectionCriteria.Forbidden (Space ((matter flavor).exteriorPower n) h d)) ↔
      SelectionCriteria.Forbidden (Space ((matter flavor).exteriorPower n) 0 0) :=
  WeakSingletHiggsReduction.all_forbidden_zero_iff ((matter flavor).exteriorPower n)
    NeutralHiggsPowers.higgs weakInclusion higgs_weak (exterior_weak flavor n)

end
end GUT.WeakSingletHiggsSupport
