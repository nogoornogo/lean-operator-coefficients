import Math.Algebra.HiggsFourWaveCubature.R0M0
import Math.Algebra.HiggsFourWaveCubature.R0M1
import Math.Algebra.HiggsFourWaveCubature.R0M2
import Math.Algebra.HiggsFourWaveCubature.R0M3
import Math.Algebra.HiggsFourWaveCubature.R0M4
import Math.Algebra.HiggsFourWaveCubature.R0M5
import Math.Algebra.HiggsFourWaveCubature.R0M6
import Math.Algebra.HiggsFourWaveCubature.R0M7
import Math.Algebra.HiggsFourWaveCubature.R0M8
import Math.Algebra.HiggsFourWaveCubature.R0M9
import Math.Algebra.HiggsFourWaveCubature.R0M10
import Math.Algebra.HiggsFourWaveCubature.R0M11
import Math.Algebra.HiggsFourWaveCubature.R0M12
import Math.Algebra.HiggsFourWaveCubature.R0M13
import Math.Algebra.HiggsFourWaveCubature.R0M14
import Math.Algebra.HiggsFourWaveCubature.R0M15
import Math.Algebra.HiggsFourWaveCubature.R0M16
import Math.Algebra.HiggsFourWaveCubature.R0M17
import Math.Algebra.HiggsFourWaveCubature.R0M18
import Math.Algebra.HiggsFourWaveCubature.R0M19
import Math.Algebra.HiggsFourWaveCubature.R0M20
import Math.Algebra.HiggsFourWaveCubature.R0M21
import Math.Algebra.HiggsFourWaveCubature.R0M22
import Math.Algebra.HiggsFourWaveCubature.R0M23
import Math.Algebra.HiggsFourWaveCubature.R0M24
import Math.Algebra.HiggsFourWaveCubature.R0M25
import Math.Algebra.HiggsFourWaveCubature.R0M26
import Math.Algebra.HiggsFourWaveCubature.R0M27
import Math.Algebra.HiggsFourWaveCubature.R0M28
import Math.Algebra.HiggsFourWaveCubature.R0M29
import Math.Algebra.HiggsFourWaveCubature.R0M30
import Math.Algebra.HiggsFourWaveCubature.R0M31
import Math.Algebra.HiggsFourWaveCubature.R0M32
import Math.Algebra.HiggsFourWaveCubature.R0M33
import Math.Algebra.HiggsFourWaveCubature.R0M34

/-! Bounded sorted-wave moment assembly. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false
def patterns : Fin 35 → Fin 4 → Fin 4 := ![![0,0,0,0],![0,0,0,1],![0,0,0,2],![0,0,0,3],![0,0,1,1],![0,0,1,2],![0,0,1,3],![0,0,2,2],![0,0,2,3],![0,0,3,3],![0,1,1,1],![0,1,1,2],![0,1,1,3],![0,1,2,2],![0,1,2,3],![0,1,3,3],![0,2,2,2],![0,2,2,3],![0,2,3,3],![0,3,3,3],![1,1,1,1],![1,1,1,2],![1,1,1,3],![1,1,2,2],![1,1,2,3],![1,1,3,3],![1,2,2,2],![1,2,2,3],![1,2,3,3],![1,3,3,3],![2,2,2,2],![2,2,2,3],![2,2,3,3],![2,3,3,3],![3,3,3,3]]
theorem sorted0 (m : Fin 35) (i j k l : Fin 4) :
    sumMoment 0 (patterns m 0) (patterns m 1) (patterns m 2) (patterns m 3) i j k l =
      expected 0 (patterns m 0) (patterns m 1) (patterns m 2) (patterns m 3) i j k l := by
  fin_cases m <;> fin_cases i
  · exact moments0_0_0 j k l
  · exact moments0_0_1 j k l
  · exact moments0_0_2 j k l
  · exact moments0_0_3 j k l
  · exact moments0_1_0 j k l
  · exact moments0_1_1 j k l
  · exact moments0_1_2 j k l
  · exact moments0_1_3 j k l
  · exact moments0_2_0 j k l
  · exact moments0_2_1 j k l
  · exact moments0_2_2 j k l
  · exact moments0_2_3 j k l
  · exact moments0_3_0 j k l
  · exact moments0_3_1 j k l
  · exact moments0_3_2 j k l
  · exact moments0_3_3 j k l
  · exact moments0_4_0 j k l
  · exact moments0_4_1 j k l
  · exact moments0_4_2 j k l
  · exact moments0_4_3 j k l
  · exact moments0_5_0 j k l
  · exact moments0_5_1 j k l
  · exact moments0_5_2 j k l
  · exact moments0_5_3 j k l
  · exact moments0_6_0 j k l
  · exact moments0_6_1 j k l
  · exact moments0_6_2 j k l
  · exact moments0_6_3 j k l
  · exact moments0_7_0 j k l
  · exact moments0_7_1 j k l
  · exact moments0_7_2 j k l
  · exact moments0_7_3 j k l
  · exact moments0_8_0 j k l
  · exact moments0_8_1 j k l
  · exact moments0_8_2 j k l
  · exact moments0_8_3 j k l
  · exact moments0_9_0 j k l
  · exact moments0_9_1 j k l
  · exact moments0_9_2 j k l
  · exact moments0_9_3 j k l
  · exact moments0_10_0 j k l
  · exact moments0_10_1 j k l
  · exact moments0_10_2 j k l
  · exact moments0_10_3 j k l
  · exact moments0_11_0 j k l
  · exact moments0_11_1 j k l
  · exact moments0_11_2 j k l
  · exact moments0_11_3 j k l
  · exact moments0_12_0 j k l
  · exact moments0_12_1 j k l
  · exact moments0_12_2 j k l
  · exact moments0_12_3 j k l
  · exact moments0_13_0 j k l
  · exact moments0_13_1 j k l
  · exact moments0_13_2 j k l
  · exact moments0_13_3 j k l
  · exact moments0_14_0 j k l
  · exact moments0_14_1 j k l
  · exact moments0_14_2 j k l
  · exact moments0_14_3 j k l
  · exact moments0_15_0 j k l
  · exact moments0_15_1 j k l
  · exact moments0_15_2 j k l
  · exact moments0_15_3 j k l
  · exact moments0_16_0 j k l
  · exact moments0_16_1 j k l
  · exact moments0_16_2 j k l
  · exact moments0_16_3 j k l
  · exact moments0_17_0 j k l
  · exact moments0_17_1 j k l
  · exact moments0_17_2 j k l
  · exact moments0_17_3 j k l
  · exact moments0_18_0 j k l
  · exact moments0_18_1 j k l
  · exact moments0_18_2 j k l
  · exact moments0_18_3 j k l
  · exact moments0_19_0 j k l
  · exact moments0_19_1 j k l
  · exact moments0_19_2 j k l
  · exact moments0_19_3 j k l
  · exact moments0_20_0 j k l
  · exact moments0_20_1 j k l
  · exact moments0_20_2 j k l
  · exact moments0_20_3 j k l
  · exact moments0_21_0 j k l
  · exact moments0_21_1 j k l
  · exact moments0_21_2 j k l
  · exact moments0_21_3 j k l
  · exact moments0_22_0 j k l
  · exact moments0_22_1 j k l
  · exact moments0_22_2 j k l
  · exact moments0_22_3 j k l
  · exact moments0_23_0 j k l
  · exact moments0_23_1 j k l
  · exact moments0_23_2 j k l
  · exact moments0_23_3 j k l
  · exact moments0_24_0 j k l
  · exact moments0_24_1 j k l
  · exact moments0_24_2 j k l
  · exact moments0_24_3 j k l
  · exact moments0_25_0 j k l
  · exact moments0_25_1 j k l
  · exact moments0_25_2 j k l
  · exact moments0_25_3 j k l
  · exact moments0_26_0 j k l
  · exact moments0_26_1 j k l
  · exact moments0_26_2 j k l
  · exact moments0_26_3 j k l
  · exact moments0_27_0 j k l
  · exact moments0_27_1 j k l
  · exact moments0_27_2 j k l
  · exact moments0_27_3 j k l
  · exact moments0_28_0 j k l
  · exact moments0_28_1 j k l
  · exact moments0_28_2 j k l
  · exact moments0_28_3 j k l
  · exact moments0_29_0 j k l
  · exact moments0_29_1 j k l
  · exact moments0_29_2 j k l
  · exact moments0_29_3 j k l
  · exact moments0_30_0 j k l
  · exact moments0_30_1 j k l
  · exact moments0_30_2 j k l
  · exact moments0_30_3 j k l
  · exact moments0_31_0 j k l
  · exact moments0_31_1 j k l
  · exact moments0_31_2 j k l
  · exact moments0_31_3 j k l
  · exact moments0_32_0 j k l
  · exact moments0_32_1 j k l
  · exact moments0_32_2 j k l
  · exact moments0_32_3 j k l
  · exact moments0_33_0 j k l
  · exact moments0_33_1 j k l
  · exact moments0_33_2 j k l
  · exact moments0_33_3 j k l
  · exact moments0_34_0 j k l
  · exact moments0_34_1 j k l
  · exact moments0_34_2 j k l
  · exact moments0_34_3 j k l
end Math.HiggsFourWaveCubature
