import Math.Algebra.HiggsFourWaveCubature.Structural.SecondCollinear

/-! Exact ordered moments, derived from the structural second-collinear identity. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false

theorem moments2_30_0 : ∀ j k l : Fin 4,
    sumMoment 2 2 2 2 2 0 j k l = expected 2 2 2 2 2 0 j k l := by
  intro j k l
  exact Structural.SecondCollinear.second_collinear_moments 2 2 2 2 0 j k l

theorem moments2_30_1 : ∀ j k l : Fin 4,
    sumMoment 2 2 2 2 2 1 j k l = expected 2 2 2 2 2 1 j k l := by
  intro j k l
  exact Structural.SecondCollinear.second_collinear_moments 2 2 2 2 1 j k l

theorem moments2_30_2 : ∀ j k l : Fin 4,
    sumMoment 2 2 2 2 2 2 j k l = expected 2 2 2 2 2 2 j k l := by
  intro j k l
  exact Structural.SecondCollinear.second_collinear_moments 2 2 2 2 2 j k l

theorem moments2_30_3 : ∀ j k l : Fin 4,
    sumMoment 2 2 2 2 2 3 j k l = expected 2 2 2 2 2 3 j k l := by
  intro j k l
  exact Structural.SecondCollinear.second_collinear_moments 2 2 2 2 3 j k l

end Math.HiggsFourWaveCubature
