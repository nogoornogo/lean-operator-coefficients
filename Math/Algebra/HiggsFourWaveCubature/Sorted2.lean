import Math.Algebra.HiggsFourWaveCubature.Sorted0
import Math.Algebra.HiggsFourWaveCubature.R2M0
import Math.Algebra.HiggsFourWaveCubature.R2M1
import Math.Algebra.HiggsFourWaveCubature.R2M2
import Math.Algebra.HiggsFourWaveCubature.R2M3
import Math.Algebra.HiggsFourWaveCubature.R2M4
import Math.Algebra.HiggsFourWaveCubature.R2M5
import Math.Algebra.HiggsFourWaveCubature.R2M6
import Math.Algebra.HiggsFourWaveCubature.R2M7
import Math.Algebra.HiggsFourWaveCubature.R2M8
import Math.Algebra.HiggsFourWaveCubature.R2M9
import Math.Algebra.HiggsFourWaveCubature.R2M10
import Math.Algebra.HiggsFourWaveCubature.R2M11
import Math.Algebra.HiggsFourWaveCubature.R2M12
import Math.Algebra.HiggsFourWaveCubature.R2M13
import Math.Algebra.HiggsFourWaveCubature.R2M14
import Math.Algebra.HiggsFourWaveCubature.R2M15
import Math.Algebra.HiggsFourWaveCubature.R2M16
import Math.Algebra.HiggsFourWaveCubature.R2M17
import Math.Algebra.HiggsFourWaveCubature.R2M18
import Math.Algebra.HiggsFourWaveCubature.R2M19
import Math.Algebra.HiggsFourWaveCubature.R2M20
import Math.Algebra.HiggsFourWaveCubature.R2M21
import Math.Algebra.HiggsFourWaveCubature.R2M22
import Math.Algebra.HiggsFourWaveCubature.R2M23
import Math.Algebra.HiggsFourWaveCubature.R2M24
import Math.Algebra.HiggsFourWaveCubature.R2M25
import Math.Algebra.HiggsFourWaveCubature.R2M26
import Math.Algebra.HiggsFourWaveCubature.R2M27
import Math.Algebra.HiggsFourWaveCubature.R2M28
import Math.Algebra.HiggsFourWaveCubature.R2M29
import Math.Algebra.HiggsFourWaveCubature.R2M30
import Math.Algebra.HiggsFourWaveCubature.R2M31
import Math.Algebra.HiggsFourWaveCubature.R2M32
import Math.Algebra.HiggsFourWaveCubature.R2M33
import Math.Algebra.HiggsFourWaveCubature.R2M34

/-! Bounded sorted-wave moment assembly. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false
theorem sorted2 (m : Fin 35) (i j k l : Fin 4) :
    sumMoment 2 (patterns m 0) (patterns m 1) (patterns m 2) (patterns m 3) i j k l =
      expected 2 (patterns m 0) (patterns m 1) (patterns m 2) (patterns m 3) i j k l := by
  fin_cases m <;> fin_cases i
  · exact moments2_0_0 j k l
  · exact moments2_0_1 j k l
  · exact moments2_0_2 j k l
  · exact moments2_0_3 j k l
  · exact moments2_1_0 j k l
  · exact moments2_1_1 j k l
  · exact moments2_1_2 j k l
  · exact moments2_1_3 j k l
  · exact moments2_2_0 j k l
  · exact moments2_2_1 j k l
  · exact moments2_2_2 j k l
  · exact moments2_2_3 j k l
  · exact moments2_3_0 j k l
  · exact moments2_3_1 j k l
  · exact moments2_3_2 j k l
  · exact moments2_3_3 j k l
  · exact moments2_4_0 j k l
  · exact moments2_4_1 j k l
  · exact moments2_4_2 j k l
  · exact moments2_4_3 j k l
  · exact moments2_5_0 j k l
  · exact moments2_5_1 j k l
  · exact moments2_5_2 j k l
  · exact moments2_5_3 j k l
  · exact moments2_6_0 j k l
  · exact moments2_6_1 j k l
  · exact moments2_6_2 j k l
  · exact moments2_6_3 j k l
  · exact moments2_7_0 j k l
  · exact moments2_7_1 j k l
  · exact moments2_7_2 j k l
  · exact moments2_7_3 j k l
  · exact moments2_8_0 j k l
  · exact moments2_8_1 j k l
  · exact moments2_8_2 j k l
  · exact moments2_8_3 j k l
  · exact moments2_9_0 j k l
  · exact moments2_9_1 j k l
  · exact moments2_9_2 j k l
  · exact moments2_9_3 j k l
  · exact moments2_10_0 j k l
  · exact moments2_10_1 j k l
  · exact moments2_10_2 j k l
  · exact moments2_10_3 j k l
  · exact moments2_11_0 j k l
  · exact moments2_11_1 j k l
  · exact moments2_11_2 j k l
  · exact moments2_11_3 j k l
  · exact moments2_12_0 j k l
  · exact moments2_12_1 j k l
  · exact moments2_12_2 j k l
  · exact moments2_12_3 j k l
  · exact moments2_13_0 j k l
  · exact moments2_13_1 j k l
  · exact moments2_13_2 j k l
  · exact moments2_13_3 j k l
  · exact moments2_14_0 j k l
  · exact moments2_14_1 j k l
  · exact moments2_14_2 j k l
  · exact moments2_14_3 j k l
  · exact moments2_15_0 j k l
  · exact moments2_15_1 j k l
  · exact moments2_15_2 j k l
  · exact moments2_15_3 j k l
  · exact moments2_16_0 j k l
  · exact moments2_16_1 j k l
  · exact moments2_16_2 j k l
  · exact moments2_16_3 j k l
  · exact moments2_17_0 j k l
  · exact moments2_17_1 j k l
  · exact moments2_17_2 j k l
  · exact moments2_17_3 j k l
  · exact moments2_18_0 j k l
  · exact moments2_18_1 j k l
  · exact moments2_18_2 j k l
  · exact moments2_18_3 j k l
  · exact moments2_19_0 j k l
  · exact moments2_19_1 j k l
  · exact moments2_19_2 j k l
  · exact moments2_19_3 j k l
  · exact moments2_20_0 j k l
  · exact moments2_20_1 j k l
  · exact moments2_20_2 j k l
  · exact moments2_20_3 j k l
  · exact moments2_21_0 j k l
  · exact moments2_21_1 j k l
  · exact moments2_21_2 j k l
  · exact moments2_21_3 j k l
  · exact moments2_22_0 j k l
  · exact moments2_22_1 j k l
  · exact moments2_22_2 j k l
  · exact moments2_22_3 j k l
  · exact moments2_23_0 j k l
  · exact moments2_23_1 j k l
  · exact moments2_23_2 j k l
  · exact moments2_23_3 j k l
  · exact moments2_24_0 j k l
  · exact moments2_24_1 j k l
  · exact moments2_24_2 j k l
  · exact moments2_24_3 j k l
  · exact moments2_25_0 j k l
  · exact moments2_25_1 j k l
  · exact moments2_25_2 j k l
  · exact moments2_25_3 j k l
  · exact moments2_26_0 j k l
  · exact moments2_26_1 j k l
  · exact moments2_26_2 j k l
  · exact moments2_26_3 j k l
  · exact moments2_27_0 j k l
  · exact moments2_27_1 j k l
  · exact moments2_27_2 j k l
  · exact moments2_27_3 j k l
  · exact moments2_28_0 j k l
  · exact moments2_28_1 j k l
  · exact moments2_28_2 j k l
  · exact moments2_28_3 j k l
  · exact moments2_29_0 j k l
  · exact moments2_29_1 j k l
  · exact moments2_29_2 j k l
  · exact moments2_29_3 j k l
  · exact moments2_30_0 j k l
  · exact moments2_30_1 j k l
  · exact moments2_30_2 j k l
  · exact moments2_30_3 j k l
  · exact moments2_31_0 j k l
  · exact moments2_31_1 j k l
  · exact moments2_31_2 j k l
  · exact moments2_31_3 j k l
  · exact moments2_32_0 j k l
  · exact moments2_32_1 j k l
  · exact moments2_32_2 j k l
  · exact moments2_32_3 j k l
  · exact moments2_33_0 j k l
  · exact moments2_33_1 j k l
  · exact moments2_33_2 j k l
  · exact moments2_33_3 j k l
  · exact moments2_34_0 j k l
  · exact moments2_34_1 j k l
  · exact moments2_34_2 j k l
  · exact moments2_34_3 j k l
end Math.HiggsFourWaveCubature
