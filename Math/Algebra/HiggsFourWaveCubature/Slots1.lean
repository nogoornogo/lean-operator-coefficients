import Math.Algebra.HiggsFourWaveCubature.Sorted
import Math.Algebra.HiggsFourWaveCubature.Symmetry

/-! Bounded wave-slot sorting; no wave-label symmetry is presumed. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false
theorem slots1 (r : Fin 3) (t u v i j k l : Fin 4) :
    sumMoment r 1 t u v i j k l = expected r 1 t u v i j k l := by
  fin_cases t <;> fin_cases u <;> fin_cases v
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 1 j k l i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12]
    exact sorted_moments r 4 j k i l
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12]
    exact sorted_moments r 5 j k i l
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12]
    exact sorted_moments r 6 j k i l
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 4 j l i k
  · rw [sum_swap01,expected_swap01]
    exact sorted_moments r 10 j i k l
  · rw [sum_swap01,expected_swap01]
    exact sorted_moments r 11 j i k l
  · rw [sum_swap01,expected_swap01]
    exact sorted_moments r 12 j i k l
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 5 j l i k
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23]
    exact sorted_moments r 11 j i l k
  · rw [sum_swap01,expected_swap01]
    exact sorted_moments r 13 j i k l
  · rw [sum_swap01,expected_swap01]
    exact sorted_moments r 14 j i k l
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 6 j l i k
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23]
    exact sorted_moments r 12 j i l k
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23]
    exact sorted_moments r 14 j i l k
  · rw [sum_swap01,expected_swap01]
    exact sorted_moments r 15 j i k l
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 4 k l i j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 10 k i j l
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 11 k i j l
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 12 k i j l
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 10 l i j k
  · exact sorted_moments r 20 i j k l
  · exact sorted_moments r 21 i j k l
  · exact sorted_moments r 22 i j k l
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 11 l i j k
  · rw [sum_swap23,expected_swap23]
    exact sorted_moments r 21 i j l k
  · exact sorted_moments r 23 i j k l
  · exact sorted_moments r 24 i j k l
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 12 l i j k
  · rw [sum_swap23,expected_swap23]
    exact sorted_moments r 22 i j l k
  · rw [sum_swap23,expected_swap23]
    exact sorted_moments r 24 i j l k
  · exact sorted_moments r 25 i j k l
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 5 k l i j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23]
    exact sorted_moments r 11 k i l j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 13 k i j l
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 14 k i j l
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 11 l i k j
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 21 i k l j
  · rw [sum_swap12,expected_swap12]
    exact sorted_moments r 23 i k j l
  · rw [sum_swap12,expected_swap12]
    exact sorted_moments r 24 i k j l
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 13 l i j k
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 23 i l j k
  · exact sorted_moments r 26 i j k l
  · exact sorted_moments r 27 i j k l
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 14 l i j k
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 24 i l j k
  · rw [sum_swap23,expected_swap23]
    exact sorted_moments r 27 i j l k
  · exact sorted_moments r 28 i j k l
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 6 k l i j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23]
    exact sorted_moments r 12 k i l j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23]
    exact sorted_moments r 14 k i l j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 15 k i j l
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 12 l i k j
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 22 i k l j
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 24 i k l j
  · rw [sum_swap12,expected_swap12]
    exact sorted_moments r 25 i k j l
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 14 l i k j
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 24 i l k j
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 27 i k l j
  · rw [sum_swap12,expected_swap12]
    exact sorted_moments r 28 i k j l
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 15 l i j k
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 25 i l j k
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 28 i l j k
  · exact sorted_moments r 29 i j k l
end Math.HiggsFourWaveCubature
