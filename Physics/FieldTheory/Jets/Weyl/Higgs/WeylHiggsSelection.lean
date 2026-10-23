import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsRelations
import Math.Algebra.Jets.MixedJetFinite

/-! Selection keeps the whole actual mixed grade and every inherited full
relation. Candidate evaluation here does not assert a coordinate equivalence. -/
namespace Physics.WeylHiggsSelection
set_option autoImplicit false
noncomputable section
open Math Math.MixedJetAlgebra PairedWeylKinetic WeylHiggsInput

@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

theorem psi_grade (c : Bool) (a : Fin 2) : psi c a ∈ grade Label Label (Fin 4) 1 0 0 := by
  simpa [psi, ScalarJetAlgebra.order] using odd_mem (B := Label) ((c,a),(0 : Fin 4 →₀ ℕ))
theorem h_grade (c : Bool) (a : Fin 2) :
    DerivativeLiteratureMixed.h c a ∈ grade Label Label (Fin 4) 0 1 0 := by
  simpa [DerivativeLiteratureMixed.h, ScalarJetAlgebra.order] using
    even_mem (F := Label) ((c,a),(0 : Fin 4 →₀ ℕ))
theorem current_grade (i : Fin 4) :
    DerivativeLiteratureMixed.current i ∈ grade Label Label (Fin 4) 2 0 0 := by
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  exact Submodule.smul_mem _ _ (mul_mem (psi_grade false a) (psi_grade true b))
theorem higgs_current_grade (i : Fin 4) :
    DerivativeLiteratureMixed.higgsCurrent i ∈ grade Label Label (Fin 4) 0 2 1 := by
  have ht (a : Fin 2) : DerivativeLiteratureMixed.h true a * D i (DerivativeLiteratureMixed.h false a) -
      D i (DerivativeLiteratureMixed.h true a) * DerivativeLiteratureMixed.h false a ∈
      grade Label Label (Fin 4) 0 2 1 :=
    Submodule.sub_mem _ (mul_mem (h_grade true a) (totalDerivative_mem i (h_grade false a)))
      (mul_mem (totalDerivative_mem i (h_grade true a)) (h_grade false a))
  exact Submodule.add_mem _ (ht 0) (ht 1)
theorem rho_grade : DerivativeLiteratureMixed.rho ∈ grade Label Label (Fin 4) 0 2 0 :=
  Submodule.add_mem _ (mul_mem (h_grade true 0) (h_grade false 0))
    (mul_mem (h_grade true 1) (h_grade false 1))
theorem candidate_grade : DerivativeLiteratureMixed.candidate ∈ V := by
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro i _
  exact mul_mem (mul_mem (current_grade i) (higgs_current_grade i)) rho_grade

def candidate : V := ⟨DerivativeLiteratureMixed.candidate, candidate_grade⟩
def evaluate : selected.Coefficient →ₗ[ℂ] ℂ where
  toFun f := f.val candidate
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem candidate_fixed (g : Group) : selected.action g candidate = candidate :=
  Subtype.ext (WeylHiggsCurrent.candidate_invariant g)

def generatedSelected := WeylHiggsRelations.generated.select V grade_stable
def selectedCoefficientEquiv : generatedSelected.Coefficient ≃ₗ[ℂ] selected.Coefficient where
  toFun f := ⟨f.val, by
    intro p hp
    apply f.property
    change p.val ∈ TwoSidedDifferential.combined D (Set.range WeylHiggsRelations.generatedSeed)
    rw [WeylHiggsRelations.generated_relations]
    exact hp⟩
  invFun f := ⟨f.val, by
    intro p hp
    apply f.property
    change p.val ∈ TwoSidedDifferential.combined D (Set.range WeylHiggsRelations.generatedSeed) at hp
    rw [WeylHiggsRelations.generated_relations] at hp
    exact hp⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem selected_extraction (f : generatedSelected.Coefficient) (p : V) :
    (selectedCoefficientEquiv f).val p = f.val p := rfl

end
end Physics.WeylHiggsSelection
