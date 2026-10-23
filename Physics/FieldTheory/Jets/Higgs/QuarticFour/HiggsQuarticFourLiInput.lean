import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourLiRelations
import Math.RepresentationTheory.Relations.SelectedRelationExtension

/-! Li's native higher-derivative densities through the actual selected input. -/
namespace Physics.HiggsQuarticFourLiInput
set_option autoImplicit false
noncomputable section
open Math MvPolynomial DerivativeLiteratureHiggs DerivativeLiteratureLiHiggs
open HiggsQuarticFourInput

theorem box_grade {n d : ℕ} {p : A} (hp : p ∈ ScalarJetAlgebra.grade n d) :
    box p ∈ ScalarJetAlgebra.grade n (d+2) :=
  Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _
    (ScalarJetAlgebra.totalDerivative_mem 0 (ScalarJetAlgebra.totalDerivative_mem 0 hp))
    (ScalarJetAlgebra.totalDerivative_mem 1 (ScalarJetAlgebra.totalDerivative_mem 1 hp)))
    (ScalarJetAlgebra.totalDerivative_mem 2 (ScalarJetAlgebra.totalDerivative_mem 2 hp)))
    (ScalarJetAlgebra.totalDerivative_mem 3 (ScalarJetAlgebra.totalDerivative_mem 3 hp))
theorem rho_grade : rho ∈ ScalarJetAlgebra.grade (S := Label) (I := Fin 4) 2 0 :=
  Submodule.add_mem _ ((h_grade true 0).mul (h_grade false 0))
    ((h_grade true 1).mul (h_grade false 1))
theorem second_grade (i j : Fin 4) :
    second i j ∈ ScalarJetAlgebra.grade (S := Label) (I := Fin 4) 2 2 :=
  Submodule.sum_mem _ (fun a _ => (h_grade true a).mul
    (ScalarJetAlgebra.totalDerivative_mem i (ScalarJetAlgebra.totalDerivative_mem j (h_grade false a))))
theorem secondDual_grade (i j : Fin 4) :
    secondDual i j ∈ ScalarJetAlgebra.grade (S := Label) (I := Fin 4) 2 2 :=
  Submodule.sum_mem _ (fun a _ =>
    (ScalarJetAlgebra.totalDerivative_mem i (ScalarJetAlgebra.totalDerivative_mem j (h_grade true a))).mul
      (h_grade false a))
theorem left_grade (i : Fin 4) :
    leftCurrent i ∈ ScalarJetAlgebra.grade (S := Label) (I := Fin 4) 2 1 :=
  Submodule.add_mem _ ((h_grade true 0).mul (first_grade false i 0))
    ((h_grade true 1).mul (first_grade false i 1))
theorem right_grade (i : Fin 4) :
    rightCurrent i ∈ ScalarJetAlgebra.grade (S := Label) (I := Fin 4) 2 1 :=
  Submodule.add_mem _ ((first_grade true i 0).mul (h_grade false 0))
    ((first_grade true i 1).mul (h_grade false 1))
theorem l1_grade : l1 ∈ V := rho_grade.mul (box_grade (box_grade rho_grade))
theorem l2_grade : l2 ∈ V := Submodule.sum_mem _ (fun i _ =>
  Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ ((second_grade i j).mul (secondDual_grade i j))))
theorem l3_grade : l3 ∈ V := Submodule.sum_mem _ (fun i _ =>
  Submodule.smul_mem _ _ ((right_grade i).mul (box_grade (left_grade i))))
def native : Fin 3 → V := ![⟨l1,l1_grade⟩,⟨l2,l2_grade⟩,⟨l3,l3_grade⟩]

def coordinate : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ) where
  toFun c := ![4*c 2,c 0,c 1-c 0-c 2]
  invFun d := ![d 1,d 2+d 1+d 0/4,d 0/4]
  left_inv c := by
    funext i
    fin_cases i <;> simp
    ring
  right_inv c := by funext i; fin_cases i <;> simp <;> ring
  map_add' c d := by funext i; fin_cases i <;> simp <;> ring
  map_smul' z c := by funext i; fin_cases i <;> simp <;> ring

theorem coefficient_values (F : selected.Coefficient) :
    (fun i => F.val (native i)) = coordinate (evaluate F) := by
  obtain ⟨f,hf,hr⟩ := SelectedRelationExtension.exists_extension P V stable F
  funext i
  fin_cases i
  · change F.val (native 0) = 4*F.val (representatives 2)
    exact (hf (native 0)).symm.trans ((HiggsQuarticFourLiRelations.l1_value f hr).trans
      (congrArg (fun z : ℂ => 4*z) (hf (representatives 2))))
  · change F.val (native 1) = F.val (representatives 0)
    exact (hf (native 1)).symm.trans ((HiggsQuarticFourLiRelations.l2_value f hr).trans
      (hf (representatives 0)))
  · change F.val (native 2) = F.val (representatives 1)-F.val (representatives 0)-F.val (representatives 2)
    calc
      _ = f l3 := (hf (native 2)).symm
      _ = f q2-f q1-f q3 := HiggsQuarticFourLiRelations.l3_value f hr
      _ = _ := congrArg₂ (fun z w : ℂ => z-w)
        (congrArg₂ (fun z w : ℂ => z-w) (hf (representatives 1)) (hf (representatives 0)))
        (hf (representatives 2))

end
end Physics.HiggsQuarticFourLiInput
