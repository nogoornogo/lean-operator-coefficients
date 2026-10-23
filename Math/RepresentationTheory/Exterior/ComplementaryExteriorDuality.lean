import TauCeti.LinearAlgebra.ExteriorPower.Basis
import TauCeti.RepresentationTheory.ExteriorPower
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
import Mathlib.Basic.Complex.Basic

/-! Equivariant complementary exterior duality for determinant-one actions.
The determinant-one hypothesis is explicit; no U(1) twist is discarded. -/
namespace Math.ComplementaryExteriorDuality
set_option autoImplicit false
noncomputable section
open Representation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] {k l : ℕ}

omit [FiniteDimensional ℂ V] in
theorem wedge_map (f : V →ₗ[ℂ] V) (x : ⋀[ℂ]^k V) (y : ⋀[ℂ]^l V) :
    exteriorPower.wedge ℂ V k l (exteriorPower.map k f x) (exteriorPower.map l f y) =
      exteriorPower.map (k+l) f (exteriorPower.wedge ℂ V k l x y) := by
  apply Subtype.ext
  simp only [exteriorPower.wedge, DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul,
    exteriorPower.coe_map, map_mul]

private theorem volume_map {t : ℕ} (h : t = Module.finrank ℂ V)
    (vol : (⋀[ℂ]^(Module.finrank ℂ V) V) →ₗ[ℂ] ℂ)
    (f : V →ₗ[ℂ] V) (hf : LinearMap.det f = 1) (x : ⋀[ℂ]^t V) :
    (h ▸ vol) (exteriorPower.map t f x) = (h ▸ vol) x := by
  subst t
  rw [LinearMap.map_exteriorPower_finrank_eq_det_smul, hf, one_smul]
  rfl

theorem pairing_invariant (rho : Representation ℂ G V)
    (hd : ∀ g, LinearMap.det (rho g) = 1)
    (vol : (⋀[ℂ]^(Module.finrank ℂ V) V) ≃ₗ[ℂ] ℂ)
    (h : k+l = Module.finrank ℂ V) (g : G)
    (x : ⋀[ℂ]^k V) (y : ⋀[ℂ]^l V) :
    exteriorPower.wedgePairing vol h (rho.exteriorPower k g x) (rho.exteriorPower l g y) =
      exteriorPower.wedgePairing vol h x y := by
  simp only [Representation.exteriorPower_apply, exteriorPower.wedgePairing,
    LinearMap.compr₂_apply]
  rw [wedge_map]
  exact volume_map h vol.toLinearMap (rho g) (hd g) _

def intertwiner (rho : Representation ℂ G V)
    (hd : ∀ g, LinearMap.det (rho g) = 1)
    (vol : (⋀[ℂ]^(Module.finrank ℂ V) V) ≃ₗ[ℂ] ℂ)
    (h : k+l = Module.finrank ℂ V) :
    IntertwiningMap (rho.exteriorPower k) (rho.exteriorPower l).dual where
  toLinearMap := exteriorPower.wedgePairing vol h
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change exteriorPower.wedgePairing vol h (rho.exteriorPower k g x) y =
      exteriorPower.wedgePairing vol h x (rho.exteriorPower l g⁻¹ y)
    have he := pairing_invariant rho hd vol h g x (rho.exteriorPower l g⁻¹ y)
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] using he

def equiv (rho : Representation ℂ G V)
    (hd : ∀ g, LinearMap.det (rho g) = 1)
    (vol : (⋀[ℂ]^(Module.finrank ℂ V) V) ≃ₗ[ℂ] ℂ)
    (h : k+l = Module.finrank ℂ V) :
    Representation.Equiv (rho.exteriorPower k) (rho.exteriorPower l).dual where
  toLinearEquiv := (exteriorPower.wedgePairing vol h).toPerfPair
  isIntertwining' := (intertwiner rho hd vol h).isIntertwining'

end
end Math.ComplementaryExteriorDuality
