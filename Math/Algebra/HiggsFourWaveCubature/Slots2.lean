import Math.Algebra.HiggsFourWaveCubature.Sorted
import Math.Algebra.HiggsFourWaveCubature.Symmetry

/-! Bounded wave-slot sorting; no wave-label symmetry is presumed. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false
theorem slots2 (r : Fin 3) (t u v i j k l : Fin 4) :
    sumMoment r 2 t u v i j k l = expected r 2 t u v i j k l := by
  fin_cases t <;> fin_cases u <;> fin_cases v
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 2 j k l i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 5 j k l i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12]
    exact sorted_moments r 7 j k i l
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12]
    exact sorted_moments r 8 j k i l
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 5 j l k i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 11 j k l i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12]
    exact sorted_moments r 13 j k i l
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12]
    exact sorted_moments r 14 j k i l
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 7 j l i k
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 13 j l i k
  · rw [sum_swap01,expected_swap01]
    exact sorted_moments r 16 j i k l
  · rw [sum_swap01,expected_swap01]
    exact sorted_moments r 17 j i k l
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 8 j l i k
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 14 j l i k
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23]
    exact sorted_moments r 17 j i l k
  · rw [sum_swap01,expected_swap01]
    exact sorted_moments r 18 j i k l
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 5 k l j i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23]
    exact sorted_moments r 11 k j l i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 13 k j i l
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 14 k j i l
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 11 l j k i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 21 j k l i
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12]
    exact sorted_moments r 23 j k i l
  · rw [sum_swap01,expected_swap01,sum_swap12,expected_swap12]
    exact sorted_moments r 24 j k i l
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 13 l j i k
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 23 j l i k
  · rw [sum_swap01,expected_swap01]
    exact sorted_moments r 26 j i k l
  · rw [sum_swap01,expected_swap01]
    exact sorted_moments r 27 j i k l
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 14 l j i k
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 24 j l i k
  · rw [sum_swap01,expected_swap01,sum_swap23,expected_swap23]
    exact sorted_moments r 27 j i l k
  · rw [sum_swap01,expected_swap01]
    exact sorted_moments r 28 j i k l
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 7 k l i j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 13 k l i j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 16 k i j l
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 17 k i j l
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 13 l k i j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 23 k l i j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 26 k i j l
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 27 k i j l
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 16 l i j k
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 26 l i j k
  · exact sorted_moments r 30 i j k l
  · exact sorted_moments r 31 i j k l
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 17 l i j k
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 27 l i j k
  · rw [sum_swap23,expected_swap23]
    exact sorted_moments r 31 i j l k
  · exact sorted_moments r 32 i j k l
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 8 k l i j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 14 k l i j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23]
    exact sorted_moments r 17 k i l j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 18 k i j l
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 14 l k i j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 24 k l i j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01,sum_swap23,expected_swap23]
    exact sorted_moments r 27 k i l j
  · rw [sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 28 k i j l
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 17 l i k j
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 27 l i k j
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 31 i k l j
  · rw [sum_swap12,expected_swap12]
    exact sorted_moments r 32 i k j l
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 18 l i j k
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12,sum_swap01,expected_swap01]
    exact sorted_moments r 28 l i j k
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 32 i l j k
  · exact sorted_moments r 33 i j k l
end Math.HiggsFourWaveCubature
