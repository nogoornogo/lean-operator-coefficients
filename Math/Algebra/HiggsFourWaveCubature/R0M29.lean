import Math.Algebra.HiggsFourWaveCubature.Structural.TransverseMoments

/-! Exact ordered moments, derived from the structural transverse identity. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false

theorem moments0_29_0 : ∀ j k l : Fin 4,
    sumMoment 0 1 3 3 3 0 j k l = expected 0 1 3 3 3 0 j k l := by
  intro j k l
  exact Structural.Transverse.transverse_moments 1 3 3 3 0 j k l

theorem moments0_29_1 : ∀ j k l : Fin 4,
    sumMoment 0 1 3 3 3 1 j k l = expected 0 1 3 3 3 1 j k l := by
  intro j k l
  exact Structural.Transverse.transverse_moments 1 3 3 3 1 j k l

theorem moments0_29_2 : ∀ j k l : Fin 4,
    sumMoment 0 1 3 3 3 2 j k l = expected 0 1 3 3 3 2 j k l := by
  intro j k l
  exact Structural.Transverse.transverse_moments 1 3 3 3 2 j k l

theorem moments0_29_3 : ∀ j k l : Fin 4,
    sumMoment 0 1 3 3 3 3 j k l = expected 0 1 3 3 3 3 j k l := by
  intro j k l
  exact Structural.Transverse.transverse_moments 1 3 3 3 3 j k l

end Math.HiggsFourWaveCubature
