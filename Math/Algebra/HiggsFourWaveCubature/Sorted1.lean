import Math.Algebra.HiggsFourWaveCubature.Sorted0
import Math.Algebra.HiggsFourWaveCubature.R1M0
import Math.Algebra.HiggsFourWaveCubature.R1M1
import Math.Algebra.HiggsFourWaveCubature.R1M2
import Math.Algebra.HiggsFourWaveCubature.R1M3
import Math.Algebra.HiggsFourWaveCubature.R1M4
import Math.Algebra.HiggsFourWaveCubature.R1M5
import Math.Algebra.HiggsFourWaveCubature.R1M6
import Math.Algebra.HiggsFourWaveCubature.R1M7
import Math.Algebra.HiggsFourWaveCubature.R1M8
import Math.Algebra.HiggsFourWaveCubature.R1M9
import Math.Algebra.HiggsFourWaveCubature.R1M10
import Math.Algebra.HiggsFourWaveCubature.R1M11
import Math.Algebra.HiggsFourWaveCubature.R1M12
import Math.Algebra.HiggsFourWaveCubature.R1M13
import Math.Algebra.HiggsFourWaveCubature.R1M14
import Math.Algebra.HiggsFourWaveCubature.R1M15
import Math.Algebra.HiggsFourWaveCubature.R1M16
import Math.Algebra.HiggsFourWaveCubature.R1M17
import Math.Algebra.HiggsFourWaveCubature.R1M18
import Math.Algebra.HiggsFourWaveCubature.R1M19
import Math.Algebra.HiggsFourWaveCubature.R1M20
import Math.Algebra.HiggsFourWaveCubature.R1M21
import Math.Algebra.HiggsFourWaveCubature.R1M22
import Math.Algebra.HiggsFourWaveCubature.R1M23
import Math.Algebra.HiggsFourWaveCubature.R1M24
import Math.Algebra.HiggsFourWaveCubature.R1M25
import Math.Algebra.HiggsFourWaveCubature.R1M26
import Math.Algebra.HiggsFourWaveCubature.R1M27
import Math.Algebra.HiggsFourWaveCubature.R1M28
import Math.Algebra.HiggsFourWaveCubature.R1M29
import Math.Algebra.HiggsFourWaveCubature.R1M30
import Math.Algebra.HiggsFourWaveCubature.R1M31
import Math.Algebra.HiggsFourWaveCubature.R1M32
import Math.Algebra.HiggsFourWaveCubature.R1M33
import Math.Algebra.HiggsFourWaveCubature.R1M34

/-! Bounded sorted-wave moment assembly. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false
theorem sorted1 (m : Fin 35) (i j k l : Fin 4) :
    sumMoment 1 (patterns m 0) (patterns m 1) (patterns m 2) (patterns m 3) i j k l =
      expected 1 (patterns m 0) (patterns m 1) (patterns m 2) (patterns m 3) i j k l := by
  fin_cases m <;> fin_cases i
  · exact moments1_0_0 j k l
  · exact moments1_0_1 j k l
  · exact moments1_0_2 j k l
  · exact moments1_0_3 j k l
  · exact moments1_1_0 j k l
  · exact moments1_1_1 j k l
  · exact moments1_1_2 j k l
  · exact moments1_1_3 j k l
  · exact moments1_2_0 j k l
  · exact moments1_2_1 j k l
  · exact moments1_2_2 j k l
  · exact moments1_2_3 j k l
  · exact moments1_3_0 j k l
  · exact moments1_3_1 j k l
  · exact moments1_3_2 j k l
  · exact moments1_3_3 j k l
  · exact moments1_4_0 j k l
  · exact moments1_4_1 j k l
  · exact moments1_4_2 j k l
  · exact moments1_4_3 j k l
  · exact moments1_5_0 j k l
  · exact moments1_5_1 j k l
  · exact moments1_5_2 j k l
  · exact moments1_5_3 j k l
  · exact moments1_6_0 j k l
  · exact moments1_6_1 j k l
  · exact moments1_6_2 j k l
  · exact moments1_6_3 j k l
  · exact moments1_7_0 j k l
  · exact moments1_7_1 j k l
  · exact moments1_7_2 j k l
  · exact moments1_7_3 j k l
  · exact moments1_8_0 j k l
  · exact moments1_8_1 j k l
  · exact moments1_8_2 j k l
  · exact moments1_8_3 j k l
  · exact moments1_9_0 j k l
  · exact moments1_9_1 j k l
  · exact moments1_9_2 j k l
  · exact moments1_9_3 j k l
  · exact moments1_10_0 j k l
  · exact moments1_10_1 j k l
  · exact moments1_10_2 j k l
  · exact moments1_10_3 j k l
  · exact moments1_11_0 j k l
  · exact moments1_11_1 j k l
  · exact moments1_11_2 j k l
  · exact moments1_11_3 j k l
  · exact moments1_12_0 j k l
  · exact moments1_12_1 j k l
  · exact moments1_12_2 j k l
  · exact moments1_12_3 j k l
  · exact moments1_13_0 j k l
  · exact moments1_13_1 j k l
  · exact moments1_13_2 j k l
  · exact moments1_13_3 j k l
  · exact moments1_14_0 j k l
  · exact moments1_14_1 j k l
  · exact moments1_14_2 j k l
  · exact moments1_14_3 j k l
  · exact moments1_15_0 j k l
  · exact moments1_15_1 j k l
  · exact moments1_15_2 j k l
  · exact moments1_15_3 j k l
  · exact moments1_16_0 j k l
  · exact moments1_16_1 j k l
  · exact moments1_16_2 j k l
  · exact moments1_16_3 j k l
  · exact moments1_17_0 j k l
  · exact moments1_17_1 j k l
  · exact moments1_17_2 j k l
  · exact moments1_17_3 j k l
  · exact moments1_18_0 j k l
  · exact moments1_18_1 j k l
  · exact moments1_18_2 j k l
  · exact moments1_18_3 j k l
  · exact moments1_19_0 j k l
  · exact moments1_19_1 j k l
  · exact moments1_19_2 j k l
  · exact moments1_19_3 j k l
  · exact moments1_20_0 j k l
  · exact moments1_20_1 j k l
  · exact moments1_20_2 j k l
  · exact moments1_20_3 j k l
  · exact moments1_21_0 j k l
  · exact moments1_21_1 j k l
  · exact moments1_21_2 j k l
  · exact moments1_21_3 j k l
  · exact moments1_22_0 j k l
  · exact moments1_22_1 j k l
  · exact moments1_22_2 j k l
  · exact moments1_22_3 j k l
  · exact moments1_23_0 j k l
  · exact moments1_23_1 j k l
  · exact moments1_23_2 j k l
  · exact moments1_23_3 j k l
  · exact moments1_24_0 j k l
  · exact moments1_24_1 j k l
  · exact moments1_24_2 j k l
  · exact moments1_24_3 j k l
  · exact moments1_25_0 j k l
  · exact moments1_25_1 j k l
  · exact moments1_25_2 j k l
  · exact moments1_25_3 j k l
  · exact moments1_26_0 j k l
  · exact moments1_26_1 j k l
  · exact moments1_26_2 j k l
  · exact moments1_26_3 j k l
  · exact moments1_27_0 j k l
  · exact moments1_27_1 j k l
  · exact moments1_27_2 j k l
  · exact moments1_27_3 j k l
  · exact moments1_28_0 j k l
  · exact moments1_28_1 j k l
  · exact moments1_28_2 j k l
  · exact moments1_28_3 j k l
  · exact moments1_29_0 j k l
  · exact moments1_29_1 j k l
  · exact moments1_29_2 j k l
  · exact moments1_29_3 j k l
  · exact moments1_30_0 j k l
  · exact moments1_30_1 j k l
  · exact moments1_30_2 j k l
  · exact moments1_30_3 j k l
  · exact moments1_31_0 j k l
  · exact moments1_31_1 j k l
  · exact moments1_31_2 j k l
  · exact moments1_31_3 j k l
  · exact moments1_32_0 j k l
  · exact moments1_32_1 j k l
  · exact moments1_32_2 j k l
  · exact moments1_32_3 j k l
  · exact moments1_33_0 j k l
  · exact moments1_33_1 j k l
  · exact moments1_33_2 j k l
  · exact moments1_33_3 j k l
  · exact moments1_34_0 j k l
  · exact moments1_34_1 j k l
  · exact moments1_34_2 j k l
  · exact moments1_34_3 j k l
end Math.HiggsFourWaveCubature
