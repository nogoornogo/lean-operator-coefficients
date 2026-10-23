import Math.Algebra.ScalarFourWaveCubature.Basic

/-! Generated exact moment identities, checked by kernel reduction. -/
namespace Math.ScalarFourWaveCubature
set_option autoImplicit false

theorem moments00 : ∀ j k l : Fin 4, sumMoment 0 0 j k l = expected 0 0 j k l := by
  decide +kernel

theorem moments01 : ∀ j k l : Fin 4, sumMoment 0 1 j k l = expected 0 1 j k l := by
  decide +kernel

theorem moments02 : ∀ j k l : Fin 4, sumMoment 0 2 j k l = expected 0 2 j k l := by
  decide +kernel

theorem moments03 : ∀ j k l : Fin 4, sumMoment 0 3 j k l = expected 0 3 j k l := by
  decide +kernel

end Math.ScalarFourWaveCubature
