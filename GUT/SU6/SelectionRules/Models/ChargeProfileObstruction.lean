import GUT.SU6.SelectionRules.Models.CyclicPatternOrbits

namespace GUT.SU6ChargeProfileObstruction
set_option autoImplicit false

def singleProfile (a q : ZMod 5) : ℤ := if q = a then 1 else 0

theorem singleProfile_injective : Function.Injective singleProfile := by
  intro a b h
  by_contra hn
  have he := congrFun h a
  simp [singleProfile, hn] at he

/-- Conditional exact-light index gate; actual mass/index transport is not assumed proved. -/
theorem equal_profiles_force_neutral (qQ qU qE : ZMod 5)
    (hu : singleProfile qQ = singleProfile qU)
    (he : singleProfile qQ = singleProfile qE) :
    2*qQ-qU-qE = 0 := by
  have hU := singleProfile_injective hu
  have hE := singleProfile_injective he
  rw [← hU, ← hE]
  ring

end GUT.SU6ChargeProfileObstruction
