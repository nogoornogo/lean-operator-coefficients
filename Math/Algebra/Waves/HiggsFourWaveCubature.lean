import Math.Algebra.HiggsFourWaveCubature.Slots0
import Math.Algebra.HiggsFourWaveCubature.Slots1
import Math.Algebra.HiggsFourWaveCubature.Slots2
import Math.Algebra.HiggsFourWaveCubature.Slots3

/-! Complete ordered fourth moments, without a group-generation premise. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false
theorem moments (r : Fin 3) (s t u v i j k l : Fin 4) :
    sumMoment r s t u v i j k l = expected r s t u v i j k l := by
  fin_cases s
  · exact slots0 r t u v i j k l
  · exact slots1 r t u v i j k l
  · exact slots2 r t u v i j k l
  · exact slots3 r t u v i j k l
end Math.HiggsFourWaveCubature
