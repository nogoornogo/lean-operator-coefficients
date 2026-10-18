import Math.RepresentationTheory.Characters.CharacterExact
import GUT.SU5.Representations.Matter
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic

namespace GUT.SU5.ExoticWedgeKernel
set_option autoImplicit false
noncomputable section
open Matter StandardModelEmbedding Representation
open scoped TensorProduct

abbrev Cube := ⋀[ℂ]^3 Five

def wedgeLinear : Five ⊗[ℂ] Ten →ₗ[ℂ] Cube :=
  TensorProduct.lift ((exteriorPower.alternatingMapLinearEquiv :
    (Five [⋀^Fin 2]→ₗ[ℂ] Cube) ≃ₗ[ℂ] (Ten →ₗ[ℂ] Cube)).toLinearMap.comp
      (exteriorPower.ιMulti ℂ 3).curryLeft)

@[simp] theorem wedge_tmul (x : Five) (v : Fin 2 → Five) :
    wedgeLinear (x ⊗ₜ[ℂ] exteriorPower.ιMulti ℂ 2 v) =
      exteriorPower.ιMulti ℂ 3 (Matrix.vecCons x v) := by
  simp [wedgeLinear, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.curryLeft_apply_apply]

def wedgeMap : IntertwiningMap (fundamental.tprod ten) (fundamental.exteriorPower 3) where
  toLinearMap := wedgeLinear
  isIntertwining' g := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change wedgeLinear (fundamental g x ⊗ₜ[ℂ]
      (fundamental.exteriorPower 2) g (exteriorPower.ιMulti ℂ 2 v)) =
      (fundamental.exteriorPower 3) g (wedgeLinear (x ⊗ₜ[ℂ] exteriorPower.ιMulti ℂ 2 v))
    rw [Representation.exteriorPower_apply_ιMulti, wedge_tmul, wedge_tmul,
      Representation.exteriorPower_apply_ιMulti]
    congr 1
    funext i
    fin_cases i <;> rfl

abbrev kernel := wedgeMap.ker
local instance : AddCommGroup kernel.toSubmodule := inferInstance
local instance : Module ℂ kernel.toSubmodule := inferInstance
abbrev representation := kernel.toRepresentation.dual

theorem wedge_surjective : Function.Surjective wedgeLinear := by
  rw [← LinearMap.range_eq_top]
  apply top_le_iff.mp
  rw [← exteriorPower.ιMulti_span ℂ 3]
  apply Submodule.span_le.mpr
  rintro _ ⟨v,rfl⟩
  refine ⟨v 0 ⊗ₜ[ℂ] exteriorPower.ιMulti ℂ 2 (fun i => v i.succ), ?_⟩
  rw [wedge_tmul]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem kernel_finrank : Module.finrank ℂ kernel.toSubmodule = 40 := by
  have hd := LinearMap.finrank_range_add_finrank_ker wedgeLinear
  rw [LinearMap.range_eq_top.mpr wedge_surjective, finrank_top] at hd
  have hdom : Module.finrank ℂ (Five ⊗[ℂ] Ten) = 50 := by
    norm_num [Module.finrank_tensorProduct, Five, Ten, exteriorPower.finrank_eq, Nat.choose]
  have hcod : Module.finrank ℂ Cube = 10 := by
    norm_num [Cube, Five, exteriorPower.finrank_eq, Nat.choose]
  rw [hdom,hcod] at hd
  change Module.finrank ℂ (LinearMap.ker wedgeLinear) = 40
  omega

theorem representation_finrank : Module.finrank ℂ (Module.Dual ℂ kernel.toSubmodule) = 40 := by
  simpa using (Subspace.dual_finrank_eq (K := ℂ) (V := kernel.toSubmodule)).trans kernel_finrank
/-- Actual trace identity from the proved exact sequence, not supplied character data. -/
theorem kernel_character (g : TargetGroup) :
    kernel.toRepresentation.character g = (fundamental.tprod ten).character g -
      (fundamental.exteriorPower 3).character g := by
  have hh : (fundamental.tprod ten).character g = kernel.toRepresentation.character g +
      (fundamental.exteriorPower 3).character g := by
    apply Math.CharacterExact.character_eq_add_of_exact
      (Math.CharacterExact.subtypeIntertwiner wedgeMap.ker) wedgeMap
      Subtype.val_injective wedge_surjective
    apply LinearMap.exact_iff.mpr
    change LinearMap.ker wedgeMap.toLinearMap =
      LinearMap.range wedgeMap.ker.toSubmodule.subtype
    rw [Submodule.range_subtype]
    rfl
  exact eq_sub_of_add_eq hh.symm

theorem representation_character (g : TargetGroup) :
    representation.character g = (fundamental.tprod ten).character g⁻¹ -
      (fundamental.exteriorPower 3).character g⁻¹ := by
  change kernel.toRepresentation.dual.character g = _
  rw [Representation.char_dual, kernel_character]
end
end GUT.SU5.ExoticWedgeKernel
