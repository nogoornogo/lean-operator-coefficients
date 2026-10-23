import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-! Exterior functoriality intertwines creation and contraction, with the
covector pulled back in the opposite direction. No gauge group is used. -/

set_option autoImplicit false

namespace Math.ExteriorNaturality

noncomputable section

variable {K V W : Type*} [CommRing K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem map_contract (f : V →ₗ[K] W) (d : Module.Dual K W) (s : ExteriorAlgebra K V) :
    ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (d.comp f) s) =
      CliffordAlgebra.contractLeft d (ExteriorAlgebra.map f s) := by
  induction s using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul v s hs =>
    simp only [CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul,
      ExteriorAlgebra.map_apply_ι, LinearMap.comp_apply, hs]

def mapEquiv (e : V ≃ₗ[K] W) : ExteriorAlgebra K V ≃ₐ[K] ExteriorAlgebra K W :=
  AlgEquiv.ofAlgHom (ExteriorAlgebra.map e.toLinearMap) (ExteriorAlgebra.map e.symm.toLinearMap)
    (by rw [ExteriorAlgebra.map_comp_map, LinearEquiv.comp_symm, ExteriorAlgebra.map_id])
    (by rw [ExteriorAlgebra.map_comp_map, LinearEquiv.symm_comp, ExteriorAlgebra.map_id])

@[simp] theorem mapEquiv_ι (e : V ≃ₗ[K] W) (v : V) :
    mapEquiv e (ExteriorAlgebra.ι K v) = ExteriorAlgebra.ι K (e v) :=
  ExteriorAlgebra.map_apply_ι _ _

theorem mapEquiv_contract (e : V ≃ₗ[K] W) (d : Module.Dual K V)
    (s : ExteriorAlgebra K V) :
    mapEquiv e (CliffordAlgebra.contractLeft d s) =
      CliffordAlgebra.contractLeft (d.comp e.symm.toLinearMap) (mapEquiv e s) := by
  have h : (d.comp e.symm.toLinearMap).comp e.toLinearMap = d := by ext v; simp
  simpa only [mapEquiv, AlgEquiv.ofAlgHom_apply, h] using
    map_contract e.toLinearMap (d.comp e.symm.toLinearMap) s

theorem mapEquiv_creation (e : V ≃ₗ[K] W) (v : V) (s : ExteriorAlgebra K V) :
    mapEquiv e (ExteriorAlgebra.ι K v * s) = ExteriorAlgebra.ι K (e v) * mapEquiv e s := by
  rw [map_mul, mapEquiv_ι]

end

end Math.ExteriorNaturality
