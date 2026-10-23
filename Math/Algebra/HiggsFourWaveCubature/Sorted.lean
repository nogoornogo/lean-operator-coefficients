import Math.Algebra.HiggsFourWaveCubature.Sorted0
import Math.Algebra.HiggsFourWaveCubature.Sorted1
import Math.Algebra.HiggsFourWaveCubature.Sorted2

/-! All sorted-wave fourth moments. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false

theorem sorted_moments (r : Fin 3) (m : Fin 35) (i j k l : Fin 4) :
    sumMoment r (patterns m 0) (patterns m 1) (patterns m 2) (patterns m 3) i j k l =
      expected r (patterns m 0) (patterns m 1) (patterns m 2) (patterns m 3) i j k l := by
  fin_cases r
  · exact sorted0 m i j k l
  · exact sorted1 m i j k l
  · exact sorted2 m i j k l
end Math.HiggsFourWaveCubature
