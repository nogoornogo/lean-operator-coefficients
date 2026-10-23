import Math.Algebra.HiggsFourWaveCubature.Basic

/-! Simultaneous wave/direction permutations of ordered fourth moments. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false

theorem metric_symm : ∀ i j : Fin 4, metric i j = metric j i := by decide +kernel
theorem gram_symm (r : Fin 3) : ∀ s t : Fin 4, gram r s t = gram r t s := by
  fin_cases r <;> decide +kernel

theorem sum_swap01 (r : Fin 3) (s t u v i j k l : Fin 4) :
    sumMoment r s t u v i j k l = sumMoment r t s u v j i k l := by
  unfold sumMoment
  apply Finset.sum_congr rfl
  intro a _
  ring
theorem sum_swap12 (r : Fin 3) (s t u v i j k l : Fin 4) :
    sumMoment r s t u v i j k l = sumMoment r s u t v i k j l := by
  unfold sumMoment
  apply Finset.sum_congr rfl
  intro a _
  ring
theorem sum_swap23 (r : Fin 3) (s t u v i j k l : Fin 4) :
    sumMoment r s t u v i j k l = sumMoment r s t v u i j l k := by
  unfold sumMoment
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem expected_swap01 (r : Fin 3) (s t u v i j k l : Fin 4) :
    expected r s t u v i j k l = expected r t s u v j i k l := by
  unfold expected
  rw [gram_symm r t s,metric_symm j i]
  ring
theorem expected_swap12 (r : Fin 3) (s t u v i j k l : Fin 4) :
    expected r s t u v i j k l = expected r s u t v i k j l := by
  unfold expected
  rw [gram_symm r u t,metric_symm k j]
  ring
theorem expected_swap23 (r : Fin 3) (s t u v i j k l : Fin 4) :
    expected r s t u v i j k l = expected r s t v u i j l k := by
  unfold expected
  rw [gram_symm r v u,metric_symm l k]
  ring

end Math.HiggsFourWaveCubature
