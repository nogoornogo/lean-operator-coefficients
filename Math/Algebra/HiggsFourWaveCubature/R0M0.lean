import Math.Algebra.HiggsFourWaveCubature.Structural.TransverseMoments

/-! Exact ordered moments, derived from the structural transverse identity. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false

theorem moments0_0_0 : ∀ j k l : Fin 4,
    sumMoment 0 0 0 0 0 0 j k l = expected 0 0 0 0 0 0 j k l := by
  intro j k l
  exact Structural.Transverse.transverse_moments 0 0 0 0 0 j k l

theorem moments0_0_1 : ∀ j k l : Fin 4,
    sumMoment 0 0 0 0 0 1 j k l = expected 0 0 0 0 0 1 j k l := by
  intro j k l
  exact Structural.Transverse.transverse_moments 0 0 0 0 1 j k l

theorem moments0_0_2 : ∀ j k l : Fin 4,
    sumMoment 0 0 0 0 0 2 j k l = expected 0 0 0 0 0 2 j k l := by
  intro j k l
  exact Structural.Transverse.transverse_moments 0 0 0 0 2 j k l

theorem moments0_0_3 : ∀ j k l : Fin 4,
    sumMoment 0 0 0 0 0 3 j k l = expected 0 0 0 0 0 3 j k l := by
  intro j k l
  exact Structural.Transverse.transverse_moments 0 0 0 0 3 j k l

end Math.HiggsFourWaveCubature
