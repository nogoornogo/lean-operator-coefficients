import Math.RepresentationTheory.SymmetricPowerDescent
import TauCeti.RepresentationTheory.CharacterTwist

/-! Actual scalar-character transport of dual, symmetric and tensor actions. -/
namespace Math.CharacterTwistTransport
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (χ ψ : G →* ℂˣ) (a : Representation ℂ G V) (b : Representation ℂ G W)

def symmetric (m : ℕ) : Representation.Equiv
    ((charTwist χ a).symmetricPower m) (charTwist (χ^m) (a.symmetricPower m)) where
  toLinearEquiv := .refl ℂ _
  isIntertwining' g := by
    apply SymmetricPower.ext
    intro v
    change ((charTwist χ a).symmetricPower m) g (SymmetricPower.tprod ℂ v) =
      (charTwist (χ^m) (a.symmetricPower m)) g (SymmetricPower.tprod ℂ v)
    rw [Representation.symmetricPower_apply_tprod]
    change SymmetricPower.tprod ℂ (fun i => (χ g : ℂ) • a g (v i)) =
      ((χ^m) g : ℂ) • a.symmetricPower m g (SymmetricPower.tprod ℂ v)
    rw [Representation.symmetricPower_apply_tprod]
    change SymmetricPower.tprod ℂ (fun i => (χ g : ℂ) • a g (v i)) =
      (χ g : ℂ)^m • SymmetricPower.tprod ℂ (fun i => a g (v i))
    simpa using (SymmetricPower.tprod ℂ).map_smul_univ
      (fun _ : Fin m => (χ g : ℂ)) (fun i => a g (v i))

def dual : Representation.Equiv (charTwist χ a).dual (charTwist χ⁻¹ a.dual) where
  toLinearEquiv := .refl ℂ _
  isIntertwining' g := by
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro v
    change φ ((χ g⁻¹ : ℂ) • a g⁻¹ v) = ((χ⁻¹) g : ℂ) * φ (a g⁻¹ v)
    simp [map_smul]

def tensor : Representation.Equiv ((charTwist χ a).tprod (charTwist ψ b))
    (charTwist (χ*ψ) (a.tprod b)) where
  toLinearEquiv := .refl ℂ _
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro v w
    change ((χ g : ℂ) • a g v) ⊗ₜ[ℂ] ((ψ g : ℂ) • b g w) =
      ((χ g : ℂ)*(ψ g : ℂ)) • (a g v ⊗ₜ[ℂ] b g w)
    simp [TensorProduct.smul_tmul,TensorProduct.tmul_smul,smul_smul,mul_comm]

def alongEquiv {a : Representation ℂ G V} {b : Representation ℂ G W}
    (e : Representation.Equiv a b) : Representation.Equiv (charTwist χ a) (charTwist χ b) where
  toLinearEquiv := e.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change e ((χ g : ℂ) • a g v) = (χ g : ℂ) • b g (e v)
    rw [map_smul]
    exact congrArg ((χ g : ℂ) • ·) (e.toIntertwiningMap.isIntertwining _ _ g v)

end
end Math.CharacterTwistTransport
