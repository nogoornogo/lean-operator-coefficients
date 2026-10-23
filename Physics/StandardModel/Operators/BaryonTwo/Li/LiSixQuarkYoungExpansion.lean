import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkYoungOperators
import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkYoungData
import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkSpeciesQuotient

/-! A symbolic group-action identity connects the expanded source dictionary
to the factored Young action, for an arbitrary function on six slots. -/
namespace Physics.LiSixQuarkYoungExpansion
noncomputable section
open LiSixQuarkYoungOperators LiSixQuarkYoungData SixQuarkSpeciesQuotient
variable {A : Type*}

def functionAction (g : Fin 4) : Module.End ℂ ((Fin 6 → A) → ℂ) where
  toFun f v := f (fun i => v (slotSwap g i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def paperMap : Fin 6 → Fin 6 := ![1,3,4,5,0,2]
def paperInverse : Fin 6 → Fin 6 := ![4,0,5,1,2,3]
def repoMap (g : Fin 48) (i : Fin 6) : Fin 6 :=
  paperMap (permutationData g (paperInverse i))

def weighted (k : Fin 11) (f : (Fin 6 → A) → ℂ) (v : Fin 6 → A) : ℂ :=
  ∑ g : Fin 48, (youngWeights k g : ℂ) * f (fun i => v (repoMap g i))
def unscaled (k : Fin 11) : Module.End ℂ ((Fin 6 → A) → ℂ) :=
  down functionAction k * (if k.val < 4 then 1+functionAction 0 else 1-functionAction 0)

private theorem reindex_tuple (v : Fin 6 → A) (s : Fin 6 → Fin 6) :
    (fun i => v (s i)) = ![v (s 0),v (s 1),v (s 2),v (s 3),v (s 4),v (s 5)] := by
  ext i; fin_cases i <;> rfl

private theorem expanded_0 (f : (Fin 6 → A) → ℂ) : weighted 0 f = unscaled 0 f := by
  ext v
  have hv : ![v 0,v 1,v 2,v 3,v 4,v 5] = v := by
    ext i; fin_cases i <;> rfl
  simp [weighted, unscaled, down, shape31, alternatingThree, Module.End.mul_apply,
    functionAction, youngWeights, repoMap, paperMap, paperInverse,
    permutationData, slotSwap, Fin.sum_univ_succ, reindex_tuple,
    Equiv.swap_apply_def, hv]
  all_goals ring

private theorem expanded_2 (f : (Fin 6 → A) → ℂ) : weighted 2 f = unscaled 2 f := by
  ext v
  have hv : ![v 0,v 1,v 2,v 3,v 4,v 5] = v := by
    ext i; fin_cases i <;> rfl
  simp [weighted, unscaled, down, shape211, symmetricThree, Module.End.mul_apply,
    functionAction, youngWeights, repoMap, paperMap, paperInverse,
    permutationData, slotSwap, Fin.sum_univ_succ, reindex_tuple,
    Equiv.swap_apply_def, hv]
  all_goals ring

private theorem expanded_4 (f : (Fin 6 → A) → ℂ) : weighted 4 f = unscaled 4 f := by
  ext v
  have hv : ![v 0,v 1,v 2,v 3,v 4,v 5] = v := by
    ext i; fin_cases i <;> rfl
  simp [weighted, unscaled, down, alternatingThree, alternatingFour, Module.End.mul_apply,
    functionAction, youngWeights, repoMap, paperMap, paperInverse,
    permutationData, slotSwap, Fin.sum_univ_succ, reindex_tuple,
    Equiv.swap_apply_def, hv]
  all_goals ring

private theorem expanded_6 (f : (Fin 6 → A) → ℂ) : weighted 6 f = unscaled 6 f := by
  ext v
  have hv : ![v 0,v 1,v 2,v 3,v 4,v 5] = v := by
    ext i; fin_cases i <;> rfl
  simp [weighted, unscaled, down, shape31, alternatingThree, Module.End.mul_apply,
    functionAction, youngWeights, repoMap, paperMap, paperInverse,
    permutationData, slotSwap, Fin.sum_univ_succ, reindex_tuple,
    Equiv.swap_apply_def, hv]
  all_goals ring

private theorem expanded_7 (f : (Fin 6 → A) → ℂ) : weighted 7 f = unscaled 7 f := by
  ext v
  have hv : ![v 0,v 1,v 2,v 3,v 4,v 5] = v := by
    ext i; fin_cases i <;> rfl
  simp [weighted, unscaled, down, shape22, Module.End.mul_apply,
    functionAction, youngWeights, repoMap, paperMap, paperInverse,
    permutationData, slotSwap, Fin.sum_univ_succ, reindex_tuple,
    Equiv.swap_apply_def, hv]
  all_goals ring

private theorem expanded_9 (f : (Fin 6 → A) → ℂ) : weighted 9 f = unscaled 9 f := by
  ext v
  have hv : ![v 0,v 1,v 2,v 3,v 4,v 5] = v := by
    ext i; fin_cases i <;> rfl
  simp [weighted, unscaled, down, shape211, symmetricThree, Module.End.mul_apply,
    functionAction, youngWeights, repoMap, paperMap, paperInverse,
    permutationData, slotSwap, Fin.sum_univ_succ, reindex_tuple,
    Equiv.swap_apply_def, hv]
  all_goals ring

private theorem expanded_10 (f : (Fin 6 → A) → ℂ) : weighted 10 f = unscaled 10 f := by
  ext v
  have hv : ![v 0,v 1,v 2,v 3,v 4,v 5] = v := by
    ext i; fin_cases i <;> rfl
  simp [weighted, unscaled, down, symmetricThree, symmetricFour, Module.End.mul_apply,
    functionAction, youngWeights, repoMap, paperMap, paperInverse,
    permutationData, slotSwap, Fin.sum_univ_succ, reindex_tuple,
    Equiv.swap_apply_def, hv]
  all_goals ring

theorem expanded_eq_factored (k : Fin 11) (f : (Fin 6 → A) → ℂ) :
    weighted k f = unscaled k f := by
  fin_cases k
  · exact expanded_0 f
  · exact expanded_0 f
  · exact expanded_2 f
  · exact expanded_2 f
  · exact expanded_4 f
  · exact expanded_4 f
  · exact expanded_6 f
  · exact expanded_7 f
  · exact expanded_7 f
  · exact expanded_9 f
  · exact expanded_10 f

theorem normalization_eq_primitive (k : Fin 11) :
    (normalization k : ℂ) = primitive (K := ℂ) k := by
  fin_cases k <;> norm_num [normalization, primitive]

theorem normalized_eq_young (k : Fin 11) (f : (Fin 6 → A) → ℂ)
    (v : Fin 6 → A) :
    (∑ g : Fin 48, ((youngWeights k g / normalization k : ℚ) : ℂ) *
      f (fun i => v (repoMap g i))) = young functionAction k f v := by
  simp only [div_eq_mul_inv, Rat.cast_mul, Rat.cast_inv]
  conv_lhs =>
    arg 2; ext g
    rw [mul_right_comm]
  rw [← Finset.sum_mul]
  change weighted k f v * (normalization k : ℂ)⁻¹ = _
  rw [expanded_eq_factored, normalization_eq_primitive]
  change unscaled k f v * (primitive (K := ℂ) k)⁻¹ =
    (1 / primitive (K := ℂ) k) * unscaled k f v
  rw [one_div, mul_comm]

theorem paperInverse_paperMap (i : Fin 6) : paperInverse (paperMap i) = i := by
  fin_cases i <;> rfl

theorem repoMap_paperMap (g : Fin 48) (i : Fin 6) :
    repoMap g (paperMap i) = paperMap (permutationData g i) := by
  simp only [repoMap, paperInverse_paperMap]

end
end Physics.LiSixQuarkYoungExpansion
