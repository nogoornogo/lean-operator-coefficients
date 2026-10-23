import Math.Algebra.ScalarFourWaveCubature.Moments4

/-! Complete finite moment table; no finite group theorem is assumed. -/
namespace Math.ScalarFourWaveCubature
set_option autoImplicit false

theorem moments (r : Fin 5) (i j k l : Fin 4) : sumMoment r i j k l = expected r i j k l := by
  fin_cases r <;> fin_cases i
  · exact moments00 j k l
  · exact moments01 j k l
  · exact moments02 j k l
  · exact moments03 j k l
  · exact moments10 j k l
  · exact moments11 j k l
  · exact moments12 j k l
  · exact moments13 j k l
  · exact moments20 j k l
  · exact moments21 j k l
  · exact moments22 j k l
  · exact moments23 j k l
  · exact moments30 j k l
  · exact moments31 j k l
  · exact moments32 j k l
  · exact moments33 j k l
  · exact moments40 j k l
  · exact moments41 j k l
  · exact moments42 j k l
  · exact moments43 j k l

end Math.ScalarFourWaveCubature
