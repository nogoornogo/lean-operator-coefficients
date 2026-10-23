import Math.Algebra.HiggsFourWaveCubature.Structural.TransverseMoments

/-! Exact ordered moments, derived from the structural transverse identity. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false

theorem moments0_13_0 : ∀ j k l : Fin 4,
    sumMoment 0 0 1 2 2 0 j k l = expected 0 0 1 2 2 0 j k l := by
  intro j k l
  exact Structural.Transverse.transverse_moments 0 1 2 2 0 j k l

theorem moments0_13_1 : ∀ j k l : Fin 4,
    sumMoment 0 0 1 2 2 1 j k l = expected 0 0 1 2 2 1 j k l := by
  intro j k l
  exact Structural.Transverse.transverse_moments 0 1 2 2 1 j k l

theorem moments0_13_2 : ∀ j k l : Fin 4,
    sumMoment 0 0 1 2 2 2 j k l = expected 0 0 1 2 2 2 j k l := by
  intro j k l
  exact Structural.Transverse.transverse_moments 0 1 2 2 2 j k l

theorem moments0_13_3 : ∀ j k l : Fin 4,
    sumMoment 0 0 1 2 2 3 j k l = expected 0 0 1 2 2 3 j k l := by
  intro j k l
  exact Structural.Transverse.transverse_moments 0 1 2 2 3 j k l

end Math.HiggsFourWaveCubature
