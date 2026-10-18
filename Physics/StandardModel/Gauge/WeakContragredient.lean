import Physics.StandardModel.Gauge.StandardSMGaugeTensor
import Math.RepresentationTheory.Decomposition.SplitRepresentationProjection

/-! The weak epsilon pairing identifies the lepton with the contragredient
of the charge +3 weak block. This shared result has no ambient GUT input. -/

set_option autoImplicit false

namespace GUT.StandardSMContragredient

noncomputable section

open StandardSMGaugeTensor SMEpsilonTensor

theorem eps2Bilin_injective : Function.Injective eps2Bilin := by
  intro a b h
  have h0 := LinearMap.congr_fun h ![0, 1]
  have h1 := LinearMap.congr_fun h ![1, 0]
  funext i
  fin_cases i
  · simpa [eps2Bilin, eps2] using h0
  · simpa [eps2Bilin, eps2] using h1

def weakDualLinearEquiv : Weak ≃ₗ[ℂ] Module.Dual ℂ Weak :=
  LinearEquiv.ofBijective eps2Bilin ⟨eps2Bilin_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℂ) (V := Weak)).symm).mp eps2Bilin_injective⟩

/-- Explicit inverse probes for the algebraic epsilon identification. -/
theorem weakDualLinearEquiv_symm_apply (phi : Module.Dual ℂ Weak) :
    weakDualLinearEquiv.symm phi = ![phi (weakBasis 1), -phi (weakBasis 0)] := by
  apply weakDualLinearEquiv.injective
  rw [weakDualLinearEquiv.apply_symm_apply]
  apply (Pi.basisFun ℂ (Fin 2)).ext
  intro i
  fin_cases i <;> simp [weakDualLinearEquiv, eps2Bilin, eps2, weakBasis, Pi.basisFun_apply]

/-- Opposite charges cancel; epsilon duality does not remove hypercharge. -/
theorem eps2_twist_invariant (y : ℤ) (g : GaugeGroup) (a b : Weak) :
    eps2 (twist weak y g a) (twist weak (-y) g b) = eps2 a b := by
  have hp : phase y g * phase (-y) g = 1 := by
    change (↑(g.2.2 ^ y) : ℂ) * ↑(g.2.2 ^ (-y)) = 1
    rw [← Circle.coe_mul, ← zpow_add]
    simp
  simp only [twist, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearMap.smul_apply, eps2_smul_left, eps2_smul_right]
  change phase (-y) g * (phase y g *
    eps2 ((g.2.1 : Matrix (Fin 2) (Fin 2) ℂ).mulVec a)
      ((g.2.1 : Matrix (Fin 2) (Fin 2) ℂ).mulVec b)) = _
  rw [eps2_invariant _ g.2.1.prop.2, mul_left_comm, ← mul_assoc, hp, one_mul]

def chargedWeakDualEquiv (y : ℤ) :
    Representation.Equiv (twist weak y) (twist weak (-y)).dual where
  toLinearEquiv := weakDualLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext; intro a
    apply LinearMap.ext; intro b
    change eps2 (twist weak y g a) b = eps2 a (twist weak (-y) g⁻¹ b)
    have h := eps2_twist_invariant y g a (twist weak (-y) g⁻¹ b)
    simpa only [Representation.self_inv_apply] using h

theorem eps2_charged_invariant (g : GaugeGroup) (a b : Weak) :
    eps2 (lepton g a) (twist weak 3 g b) = eps2 a b := by
  have hp : phase (-3) g * phase 3 g = 1 := by
    change (↑(g.2.2 ^ (-3 : ℤ)) : ℂ) * ↑(g.2.2 ^ (3 : ℤ)) = 1
    rw [← Circle.coe_mul, ← zpow_add]
    norm_num
  simp only [lepton, twist, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearMap.smul_apply, eps2_smul_left, eps2_smul_right]
  change phase 3 g * (phase (-3) g *
    eps2 ((g.2.1 : Matrix (Fin 2) (Fin 2) ℂ).mulVec a)
      ((g.2.1 : Matrix (Fin 2) (Fin 2) ℂ).mulVec b)) = _
  rw [eps2_invariant _ g.2.1.prop.2, mul_left_comm, ← mul_assoc, hp, one_mul]

def leptonDualEquiv : Representation.Equiv lepton (twist weak 3).dual where
  toLinearEquiv := weakDualLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext; intro a
    apply LinearMap.ext; intro b
    change eps2 (lepton g a) b = eps2 a (twist weak 3 g⁻¹ b)
    have h := eps2_charged_invariant g a (twist weak 3 g⁻¹ b)
    simpa only [Representation.self_inv_apply] using h

end

end GUT.StandardSMContragredient
