import Math.RepresentationTheory.PointwiseGaugeRemoval

/-! Field-level group-law test for pointwise inner lifts. Centrality alone
is not a proof that the defect acts trivially on matter. -/
namespace Math.PointwiseInnerDefect
set_option autoImplicit false
noncomputable section
open Representation AutomorphismCovariantHom PointwiseGaugeRemoval
variable {k G H V : Type*} [Field k] [Group G] [Group H]
  [AddCommGroup V] [Module k V]
  (a : Representation k G V) (alpha : H →* MulAut G) (A : Action a alpha)
  (s : H → G) (hs : ∀ h g, alpha h g = s h * g * (s h)⁻¹)

/-- Multiplication defect of the supplied pointwise lift. -/
def defect (h l : H) : G := (s h * s l)⁻¹ * s (h * l)

include hs

/-- Exact multiplication law before any coinvariant projection. -/
theorem removed_mul (h l : H) :
    removed a alpha A s h * removed a alpha A s l =
      a (defect s h l) * removed a alpha A s (h * l) := by
  calc
    removed a alpha A s h * removed a alpha A s l =
        a (s l)⁻¹ * (removed a alpha A s h * A.residual l) := by
      change removed a alpha A s h * (a (s l)⁻¹ * A.residual l) = _
      rw [← mul_assoc, removed_commutes a alpha A s hs,
        mul_assoc]
    _ = a ((s h * s l)⁻¹) * A.residual (h * l) := by
      simp only [removed, mul_inv_rev, map_mul, mul_assoc]
    _ = a (defect s h l) * removed a alpha A s (h * l) := by
      simp only [defect, removed, ← mul_assoc, ← map_mul, mul_inv_cancel_right]

/-- The precise field-level obstruction is the represented defect, not the
failure of the lift itself to be a homomorphism. -/
theorem removed_mul_iff (h l : H) :
    removed a alpha A s h * removed a alpha A s l =
      removed a alpha A s (h * l) ↔ a (defect s h l) = 1 := by
  have hi : removed a alpha A s (h * l) *
      (A.residual (h * l)⁻¹ * a (s (h * l))) = 1 := by
    rw [removed, mul_assoc,
      ← mul_assoc (A.residual (h * l)) (A.residual (h * l)⁻¹) (a (s (h * l))),
      ← map_mul, mul_inv_cancel, map_one, one_mul,
      ← map_mul, inv_mul_cancel, map_one]
  constructor
  · intro he
    rw [removed_mul a alpha A s hs] at he
    have hc := congrArg (fun f : Module.End k V =>
      f * (A.residual (h * l)⁻¹ * a (s (h * l)))) he
    simpa only [mul_assoc, hi, mul_one] using hc
  · intro he
    rw [removed_mul a alpha A s hs, he, one_mul]

/-- Invisible lift defects suffice for a group law, without a homomorphic lift. -/
def removedRepresentation (h1 : s 1 = 1)
    (hd : ∀ h l, a (defect s h l) = 1) : Representation k H V where
  toFun := removed a alpha A s
  map_one' := by simp [removed, h1]
  map_mul' h l := by symm; rw [removed_mul a alpha A s hs, hd, one_mul]

theorem removedRepresentation_commutes (h1 : s 1 = 1)
    (hd : ∀ h l, a (defect s h l) = 1) (h : H) (g : G) :
    removedRepresentation a alpha A s hs h1 hd h * a g =
      a g * removedRepresentation a alpha A s hs h1 hd h :=
  removed_commutes a alpha A s hs h g

end
end Math.PointwiseInnerDefect
