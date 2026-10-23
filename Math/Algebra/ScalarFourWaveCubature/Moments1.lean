import Math.Algebra.ScalarFourWaveCubature.Moments0

/-! Generated exact moment identities, checked by kernel reduction. -/
namespace Math.ScalarFourWaveCubature
set_option autoImplicit false

theorem moments10 : ∀ j k l : Fin 4, sumMoment 1 0 j k l = expected 1 0 j k l := by
  decide +kernel

theorem moments11 : ∀ j k l : Fin 4, sumMoment 1 1 j k l = expected 1 1 j k l := by
  decide +kernel

theorem moments12 : ∀ j k l : Fin 4, sumMoment 1 2 j k l = expected 1 2 j k l := by
  decide +kernel

theorem moments13 : ∀ j k l : Fin 4, sumMoment 1 3 j k l = expected 1 3 j k l := by
  decide +kernel

end Math.ScalarFourWaveCubature
