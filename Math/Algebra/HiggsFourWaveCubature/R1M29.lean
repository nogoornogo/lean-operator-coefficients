import Math.Algebra.HiggsFourWaveCubature.Structural.CollinearMoments

/-! Exact ordered moments, derived from the structural collinear identity. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false

theorem moments1_29_0 : ∀ j k l : Fin 4,
    sumMoment 1 1 3 3 3 0 j k l = expected 1 1 3 3 3 0 j k l := by
  intro j k l
  exact Structural.collinear_moments 1 3 3 3 0 j k l

theorem moments1_29_1 : ∀ j k l : Fin 4,
    sumMoment 1 1 3 3 3 1 j k l = expected 1 1 3 3 3 1 j k l := by
  intro j k l
  exact Structural.collinear_moments 1 3 3 3 1 j k l

theorem moments1_29_2 : ∀ j k l : Fin 4,
    sumMoment 1 1 3 3 3 2 j k l = expected 1 1 3 3 3 2 j k l := by
  intro j k l
  exact Structural.collinear_moments 1 3 3 3 2 j k l

theorem moments1_29_3 : ∀ j k l : Fin 4,
    sumMoment 1 1 3 3 3 3 j k l = expected 1 1 3 3 3 3 j k l := by
  intro j k l
  exact Structural.collinear_moments 1 3 3 3 3 j k l

end Math.HiggsFourWaveCubature
