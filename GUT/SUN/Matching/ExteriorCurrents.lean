import GUT.SUN.Matching.DiagonalBackground
import GUT.SUN.Matching.ExteriorMatter

open Physics

open Math

/-! Projected currents are computed from the actual exterior action on every
massive root. No spectator-current vanishing is an input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SUN.ExteriorCurrents

noncomputable section
open DiagonalBackground ExteriorSquareBlock ExteriorSquareCoordinates SMEpsilonTensor
variable {r : ℕ} (D : Background r)

theorem cut_upper_core (i : Fin 3) (w : Fin 2) :
    cut r (D.upper (.inl (i,w))) = SU5.HeavyCurrents.upper i w := by
  change cut r (Matrix.single (Fin.castAdd r (Fin.castAdd 2 i))
    (Fin.castAdd r (Fin.natAdd 3 w)) 1) = _
  exact cut_single r _ _

theorem cut_lower_core (i : Fin 3) (w : Fin 2) :
    cut r (D.lower (.inl (i,w))) = SU5.HeavyCurrents.lower i w := by
  change cut r (Matrix.single (Fin.castAdd r (Fin.natAdd 3 w))
    (Fin.castAdd r (Fin.castAdd 2 i)) 1) = _
  exact cut_single r _ _

theorem cut_upper_extra (c : D.ExtraRoot) : cut r (D.upper (.inr c)) = 0 :=
  cut_single_extra r _ _ c.property.2.1
theorem cut_lower_extra (c : D.ExtraRoot) : cut r (D.lower (.inr c)) = 0 :=
  cut_single_extra_reverse r _ _ c.property.2.1

def upCurrent (c : D.Channel) : StandardSMGaugeTensor.Quark →ₗ[ℂ] Module.Dual ℂ Color :=
  ((LinearMap.fst ℂ _ _).comp SU5.ExteriorSquareBranching.branch).comp
    ((coreAction r (D.upper c)).comp SU5.HeavyCurrents.quarkEmbed)
def electronCurrent (c : D.Channel) : StandardSMGaugeTensor.Quark →ₗ[ℂ] Module.Dual ℂ ℂ :=
  ((LinearMap.snd ℂ _ _).comp ((LinearMap.snd ℂ _ _).comp SU5.ExteriorSquareBranching.branch)).comp
    ((coreAction r (D.lower c)).comp SU5.HeavyCurrents.quarkEmbed)

theorem upCurrent_core (i : Fin 3) (w : Fin 2) :
    upCurrent D (.inl (i,w)) = SU5.HeavyCurrents.upCurrent i w := by
  simp only [upCurrent, coreAction_eq, cut_upper_core, SU5.HeavyCurrents.upCurrent]
theorem electronCurrent_core (i : Fin 3) (w : Fin 2) :
    electronCurrent D (.inl (i,w)) = SU5.HeavyCurrents.electronCurrent i w := by
  simp only [electronCurrent, coreAction_eq, cut_lower_core, SU5.HeavyCurrents.electronCurrent]
theorem upCurrent_extra (c : D.ExtraRoot) : upCurrent D (.inr c) = 0 := by
  simp [upCurrent, coreAction_eq, cut_upper_extra, infinitesimal_zero]
theorem electronCurrent_extra (c : D.ExtraRoot) : electronCurrent D (.inr c) = 0 := by
  simp [electronCurrent, coreAction_eq, cut_lower_extra, infinitesimal_zero]

end
end GUT.SUN.ExteriorCurrents
