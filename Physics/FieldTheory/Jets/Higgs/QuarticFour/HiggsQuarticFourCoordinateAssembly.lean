import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourMomentValues

/-! Coordinate assembly from a checked finite moment family.
The public completeness module supplies the family from kernel certificates. -/
namespace Physics.HiggsQuarticFourCoordinateAssembly
set_option autoImplicit false
noncomputable section
open Math DerivativeLiteratureHiggs HiggsQuarticFourInput
open HiggsQuarticFourMomentInvariance (Moments)
variable (hM : ∀ r : Fin 3, Moments r)

def rawCoefficient (r : Fin 3) : selected.Coefficient :=
  HiggsQuarticFourMomentInvariance.coefficient r (hM r)
theorem raw_value (r i : Fin 3) : evaluate (rawCoefficient hM r) i =
    HiggsQuarticFourMomentValues.values r i :=
  HiggsQuarticFourMomentValues.representative_value r (hM r) i

def inverseMatrix : Fin 3 → Fin 3 → ℂ := ![
  ![-1/24,5/96,-1/96],![1/24,-1/96,-1/96],![-1/24,-1/96,5/96]]
def normalized (i : Fin 3) : selected.Coefficient :=
  ∑ r : Fin 3, inverseMatrix i r • rawCoefficient hM r

theorem normalized_value (i j : Fin 3) : evaluate (normalized hM i) j = if i = j then 1 else 0 := by
  calc
    _ = ∑ r : Fin 3, inverseMatrix i r*evaluate (rawCoefficient hM r) j := by
      simp only [normalized,map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    _ = ∑ r : Fin 3, inverseMatrix i r*HiggsQuarticFourMomentValues.values r j := by
      apply Finset.sum_congr rfl
      intro r _
      exact congrArg (fun v : ℂ => inverseMatrix i r*v) (raw_value hM r j)
    _ = _ := by
      fin_cases i <;> fin_cases j
      all_goals norm_num [inverseMatrix,HiggsQuarticFourMomentValues.values,Fin.sum_univ_succ]

def reconstruction : (Fin 3 → ℂ) →ₗ[ℂ] selected.Coefficient where
  toFun c := ∑ i : Fin 3, c i • normalized hM i
  map_add' c d := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' z c := by simp [Finset.smul_sum,smul_smul]

theorem evaluate_reconstruction (c : Fin 3 → ℂ) : evaluate (reconstruction hM c) = c := by
  funext j
  change evaluate (∑ i : Fin 3, c i • normalized hM i) j = c j
  calc
    _ = ∑ i : Fin 3, c i*evaluate (normalized hM i) j := by
      simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    _ = ∑ i : Fin 3, c i*(if i = j then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun v : ℂ => c i*v) (normalized_value hM i j)
    _ = _ := by simp

def equivalence : selected.Coefficient ≃ₗ[ℂ] (Fin 3 → ℂ) where
  toLinearMap := evaluate
  invFun := reconstruction hM
  left_inv F := HiggsQuarticFourUpper.evaluate_injective (evaluate_reconstruction hM (evaluate F))
  right_inv := evaluate_reconstruction hM

theorem extraction (F : selected.Coefficient) (i : Fin 3) :
    equivalence hM F i = F.val (representatives i) := rfl
theorem reconstruct (F : selected.Coefficient) : reconstruction hM (equivalence hM F) = F :=
  (equivalence hM).symm_apply_apply F
include hM in
theorem coefficient_dimension : Module.finrank ℂ selected.Coefficient = 3 := by
  rw [(equivalence hM).finrank_eq]
  simp

def directSelected := (HiggsStandardInput.direct 0 0).select V stable
def toDirect (F : selected.Coefficient) : directSelected.Coefficient := ⟨F.val,by
  intro p hp
  apply F.property
  change p.val ∈ DifferentialEquation.combined D (Math.HiggsLagrangianInput.density 0 0).scalarSeeds
  rw [Math.HiggsLagrangianInput.generated_relations]
  exact hp⟩
def toGenerated (F : directSelected.Coefficient) : selected.Coefficient := ⟨F.val,by
  intro p hp
  apply F.property
  change p.val ∈ DifferentialEquation.combined D (seeds 0 0)
  rw [← Math.HiggsLagrangianInput.generated_relations]
  exact hp⟩
def inputEquivalence : selected.Coefficient ≃ₗ[ℂ] directSelected.Coefficient where
  toFun := toDirect
  invFun := toGenerated
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def directEquivalence : directSelected.Coefficient ≃ₗ[ℂ] (Fin 3 → ℂ) :=
  inputEquivalence.symm.trans (equivalence hM)
theorem direct_extraction (F : directSelected.Coefficient) (i : Fin 3) :
    directEquivalence hM F i = F.val (representatives i) := rfl
theorem input_extraction (F : selected.Coefficient) (p : V) : (inputEquivalence F).val p = F.val p := rfl

end
end Physics.HiggsQuarticFourCoordinateAssembly
