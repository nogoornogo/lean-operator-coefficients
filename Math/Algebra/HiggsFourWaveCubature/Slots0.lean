import Math.Algebra.HiggsFourWaveCubature.Sorted
import Math.Algebra.HiggsFourWaveCubature.Symmetry

/-! Bounded wave-slot sorting; no wave-label symmetry is presumed. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false
theorem slots0 (r : Fin 3) (t u v i j k l : Fin 4) :
    sumMoment r 0 t u v i j k l = expected r 0 t u v i j k l := by
  fin_cases t <;> fin_cases u <;> fin_cases v
  · exact sorted_moments r 0 i j k l
  · exact sorted_moments r 1 i j k l
  · exact sorted_moments r 2 i j k l
  · exact sorted_moments r 3 i j k l
  · rw [sum_swap23,expected_swap23]
    exact sorted_moments r 1 i j l k
  · exact sorted_moments r 4 i j k l
  · exact sorted_moments r 5 i j k l
  · exact sorted_moments r 6 i j k l
  · rw [sum_swap23,expected_swap23]
    exact sorted_moments r 2 i j l k
  · rw [sum_swap23,expected_swap23]
    exact sorted_moments r 5 i j l k
  · exact sorted_moments r 7 i j k l
  · exact sorted_moments r 8 i j k l
  · rw [sum_swap23,expected_swap23]
    exact sorted_moments r 3 i j l k
  · rw [sum_swap23,expected_swap23]
    exact sorted_moments r 6 i j l k
  · rw [sum_swap23,expected_swap23]
    exact sorted_moments r 8 i j l k
  · exact sorted_moments r 9 i j k l
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 1 i k l j
  · rw [sum_swap12,expected_swap12]
    exact sorted_moments r 4 i k j l
  · rw [sum_swap12,expected_swap12]
    exact sorted_moments r 5 i k j l
  · rw [sum_swap12,expected_swap12]
    exact sorted_moments r 6 i k j l
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 4 i l j k
  · exact sorted_moments r 10 i j k l
  · exact sorted_moments r 11 i j k l
  · exact sorted_moments r 12 i j k l
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 5 i l j k
  · rw [sum_swap23,expected_swap23]
    exact sorted_moments r 11 i j l k
  · exact sorted_moments r 13 i j k l
  · exact sorted_moments r 14 i j k l
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 6 i l j k
  · rw [sum_swap23,expected_swap23]
    exact sorted_moments r 12 i j l k
  · rw [sum_swap23,expected_swap23]
    exact sorted_moments r 14 i j l k
  · exact sorted_moments r 15 i j k l
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 2 i k l j
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 5 i k l j
  · rw [sum_swap12,expected_swap12]
    exact sorted_moments r 7 i k j l
  · rw [sum_swap12,expected_swap12]
    exact sorted_moments r 8 i k j l
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 5 i l k j
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 11 i k l j
  · rw [sum_swap12,expected_swap12]
    exact sorted_moments r 13 i k j l
  · rw [sum_swap12,expected_swap12]
    exact sorted_moments r 14 i k j l
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 7 i l j k
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 13 i l j k
  · exact sorted_moments r 16 i j k l
  · exact sorted_moments r 17 i j k l
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 8 i l j k
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 14 i l j k
  · rw [sum_swap23,expected_swap23]
    exact sorted_moments r 17 i j l k
  · exact sorted_moments r 18 i j k l
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 3 i k l j
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 6 i k l j
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 8 i k l j
  · rw [sum_swap12,expected_swap12]
    exact sorted_moments r 9 i k j l
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 6 i l k j
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 12 i k l j
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 14 i k l j
  · rw [sum_swap12,expected_swap12]
    exact sorted_moments r 15 i k j l
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 8 i l k j
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 14 i l k j
  · rw [sum_swap12,expected_swap12,sum_swap23,expected_swap23]
    exact sorted_moments r 17 i k l j
  · rw [sum_swap12,expected_swap12]
    exact sorted_moments r 18 i k j l
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 9 i l j k
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 15 i l j k
  · rw [sum_swap23,expected_swap23,sum_swap12,expected_swap12]
    exact sorted_moments r 18 i l j k
  · exact sorted_moments r 19 i j k l
end Math.HiggsFourWaveCubature
