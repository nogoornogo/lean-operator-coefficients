import Math.RepresentationTheory.ExternalInvariantTensor

namespace Math.SymmetricInvariantPairing
set_option autoImplicit false
noncomputable section
open Representation SplitRepresentationProjection
open scoped TensorProduct
variable {H A B D R : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup D] [Module ℂ D] [AddCommGroup R] [Module ℂ R]
  {a : Representation ℂ H A} {b : Representation ℂ H B}
  {d : Representation ℂ H D} {r : Representation ℂ H R}

/-- A single projection is reused in both identical-species slots. -/
def coefficient (sa : Split a r) (sb : Split b r) (sd : Split d r) :
    IntertwiningMap ((a.tprod a).tprod (b.dual.tprod d.dual))
      (Representation.trivial ℂ H ℂ) :=
  let f := (InvariantPairing.pulledCoefficient sa.project sb.dual.project
    sa.project sd.dual.project).comp
      (OrderedInvariantPairing.swapMiddle a a b.dual d.dual).toIntertwiningMap
  f + f.comp (ExternalInvariantTensor.tensorEquiv
    (Representation.TensorProduct.comm a a)
    (Representation.Equiv.refl (b.dual.tprod d.dual))).toIntertwiningMap

@[simp] theorem apply_coefficient (sa : Split a r) (sb : Split b r) (sd : Split d r)
    (x y : A) (u : Module.Dual ℂ B) (e : Module.Dual ℂ D) :
    coefficient sa sb sd ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) =
      sb.dual.project u (sa.project x) * sd.dual.project e (sa.project y) +
      sb.dual.project u (sa.project y) * sd.dual.project e (sa.project x) := rfl

theorem diagonal (sa : Split a r) (sb : Split b r) (sd : Split d r)
    (x : R) (phi : Module.Dual ℂ R) (hphi : phi x = 1) :
    coefficient sa sb sd ((sa.embed x ⊗ₜ[ℂ] sa.embed x) ⊗ₜ[ℂ]
      (sb.dual.embed phi ⊗ₜ[ℂ] sd.dual.embed phi)) = 2 := by
  simp only [apply_coefficient, sa.left_inv, sb.dual.left_inv, sd.dual.left_inv, hphi]
  norm_num

theorem swap (sa : Split a r) (sb : Split b r) (sd : Split d r)
    (x y : A) (u : Module.Dual ℂ B) (e : Module.Dual ℂ D) :
    coefficient sa sb sd ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) =
      coefficient sa sb sd ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) := by
  simp only [apply_coefficient, add_comm]

end
end Math.SymmetricInvariantPairing
