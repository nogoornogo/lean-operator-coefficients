import Math.RepresentationTheory.AutomorphismCovariantHom
import Mathlib.RepresentationTheory.Character

/-! Normalizing linear actions preserve character probes, obstructing reversal
of probes with nonzero dual index. No automorphism classification is assumed. -/
namespace Math.CovariantCharacterObstruction
set_option autoImplicit false
noncomputable section
open Representation AutomorphismCovariantHom
variable {k G H V : Type*} [Field k] [Group G] [Group H]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  (a : Representation k G V) (alpha : H →* MulAut G) (A : Action a alpha)

include A
omit [FiniteDimensional k V] in
theorem character_invariant (h : H) (g : G) : a.character (alpha h g) = a.character g := by
  have he : A.residual h * a g = a (alpha h g) * A.residual h := by
    ext v
    exact A.covariance h g v
  have hc : A.residual h * a g * A.residual h⁻¹ = a (alpha h g) := by
    rw [he, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  change LinearMap.trace k V (a (alpha h g)) = LinearMap.trace k V (a g)
  rw [← hc, LinearMap.trace_mul_cycle, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem dual_index_zero_of_inverse (h : H) (g : G) (hg : alpha h g = g⁻¹) :
    a.character g - a.dual.character g = 0 := by
  rw [a.char_dual]
  exact sub_eq_zero.mpr ((character_invariant a alpha A h g).symm.trans
    (congrArg a.character hg))

/-- Inner gauge conjugation of the inverse probe gives the same obstruction. -/
theorem dual_index_zero_of_conjugate_inverse (h : H) (g c : G)
    (hg : alpha h g = c * g⁻¹ * c⁻¹) :
    a.character g - a.dual.character g = 0 := by
  rw [a.char_dual]
  apply sub_eq_zero.mpr
  calc
    a.character g = a.character (alpha h g) := (character_invariant a alpha A h g).symm
    _ = a.character g⁻¹ := by rw [hg, a.char_conj]

end
end Math.CovariantCharacterObstruction
