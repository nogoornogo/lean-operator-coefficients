import Math.Algebra.HiggsFourWaveCubature.Sorted
import Math.Algebra.HiggsFourWaveCubature.Symmetry

/-! Bounded wave-slot sorting; no wave-label symmetry is presumed. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false
theorem slots3 (r : Fin 3) (t u v i j k l : Fin 4) :
    sumMoment r 3 t u v i j k l = expected r 3 t u v i j k l := by
  fin_cases t <;> fin_cases u <;> fin_cases v
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 3 j k l i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 6 j k l i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 8 j k l i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12]
    exact sorted_moments r 9 j k i l
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 6 j l k i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 12 j k l i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 14 j k l i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12]
    exact sorted_moments r 15 j k i l
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 8 j l k i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 14 j l k i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 17 j k l i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12]
    exact sorted_moments r 18 j k i l
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 9 j l i k
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 15 j l i k
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 18 j l i k
  · rw [sum_swap01,expected_swap01]
    exact sorted_moments r 19 j i k l
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 6 k l j i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23]
    exact sorted_moments r 12 k j l i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23]
    exact sorted_moments r 14 k j l i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 15 k j i l
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 12 l j k i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 22 j k l i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 24 j k l i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12]
    exact sorted_moments r 25 j k i l
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 14 l j k i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 24 j l k i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 27 j k l i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12]
    exact sorted_moments r 28 j k i l
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 15 l j i k
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 25 j l i k
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 28 j l i k
  · rw [sum_swap01,expected_swap01]
    exact sorted_moments r 29 j i k l
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 8 k l j i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 14 k l j i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23]
    exact sorted_moments r 17 k j l i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 18 k j i l
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 14 l k j i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 24 k l j i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23]
    exact sorted_moments r 27 k j l i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 28 k j i l
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 17 l j k i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 27 l j k i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 31 j k l i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12]
    exact sorted_moments r 32 j k i l
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 18 l j i k
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 28 l j i k
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 32 j l i k
  · rw [sum_swap01,expected_swap01]
    exact sorted_moments r 33 j i k l
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 9 k l i j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 15 k l i j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 18 k l i j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 19 k i j l
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 15 l k i j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 25 k l i j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 28 k l i j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 29 k i j l
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 18 l k i j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 28 l k i j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 32 k l i j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 33 k i j l
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 19 l i j k
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 29 l i j k
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 33 l i j k
  · exact sorted_moments r 34 i j k l
end Math.HiggsFourWaveCubature
