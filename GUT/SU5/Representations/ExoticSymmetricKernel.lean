import Math.RepresentationTheory.Characters.CharacterExact
import GUT.SU5.Representations.ExoticWedgeKernel
import Math.RepresentationTheory.TensorSquareMultilinear
import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
import TauCeti.LinearAlgebra.SymmetricPower.Basis

namespace GUT.SU5.ExoticSymmetricKernel
set_option autoImplicit false
noncomputable section
open Matter StandardModelEmbedding Representation Math
open scoped TensorProduct
abbrev Fourth := ⋀[ℂ]^4 Five
local instance : AddCommGroup Ten := inferInstance
local instance : Module ℂ Ten := inferInstance
local instance : AddCommGroup Fourth := inferInstance
local instance : Module ℂ Fourth := inferInstance
abbrev product := exteriorPower.wedge ℂ Five 2 2

theorem product_comm : (product : Ten →ₗ[ℂ] Ten →ₗ[ℂ] Fourth) = product.flip := by
  refine exteriorPower.linearMap_ext (R := ℂ) (n := 2) (M := Five)
    (N := Ten →ₗ[ℂ] Fourth) ?_
  apply AlternatingMap.ext
  intro u
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  apply Subtype.ext
  change ExteriorAlgebra.ιMulti ℂ 2 u * ExteriorAlgebra.ιMulti ℂ 2 v =
    ExteriorAlgebra.ιMulti ℂ 2 v * ExteriorAlgebra.ιMulti ℂ 2 u
  have hs : (-1 : ℤˣ)^(2*2) = 1 := by decide
  simpa only [hs, one_smul] using ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm (R := ℂ) u v

def multi : MultilinearMap ℂ (fun _ : Fin 2 => Ten) Fourth :=
  TensorSquareMultilinear.toMultilinear (TensorProduct.lift product)

theorem multi_symmetric : SymmetricSquareDescent.IsSymmetric multi := by
  intro e v
  rcases TauCeti.perm_fin_two_eq_one_or_swap e with he | he
  · subst e; rfl
  · subst e
    change product (v 1) (v 0) = product (v 0) (v 1)
    exact congrArg (fun f : Ten →ₗ[ℂ] Ten →ₗ[ℂ] Fourth => f (v 1) (v 0)) product_comm

theorem product_covariant (g : TargetGroup) (x y : Ten) :
    product (ten g x) (ten g y) = (fundamental.exteriorPower 4) g (product x y) := by
  apply Subtype.ext
  change (exteriorPower.map 2 (fundamental g) x : ExteriorAlgebra ℂ Five) *
    (exteriorPower.map 2 (fundamental g) y : ExteriorAlgebra ℂ Five) =
    (exteriorPower.map 4 (fundamental g) (product x y) : ExteriorAlgebra ℂ Five)
  simp only [exteriorPower.coe_map]
  exact (map_mul (ExteriorAlgebra.map (fundamental g)) x.val y.val).symm

def wedgeMap : IntertwiningMap (ten.symmetricPower 2) (fundamental.exteriorPower 4) :=
  SymmetricSquareDescent.descend ten (fundamental.exteriorPower 4)
    ⟨⟨multi,multi_symmetric⟩, fun g v => product_covariant g (v 0) (v 1)⟩

@[simp] theorem wedge_tprod (v : Fin 2 → Ten) :
    wedgeMap (SymmetricPower.tprod ℂ v) = product (v 0) (v 1)  := by
  exact SymmetricSquareDescent.lift_tprod multi multi_symmetric v

abbrev kernel := wedgeMap.ker
local instance : AddCommGroup kernel.toSubmodule := inferInstance
local instance : Module ℂ kernel.toSubmodule := inferInstance
abbrev representation := kernel.toRepresentation

theorem wedge_surjective : Function.Surjective wedgeMap.toLinearMap := by
  rw [← LinearMap.range_eq_top]
  apply top_le_iff.mp
  rw [← exteriorPower.ιMulti_span ℂ 4]
  apply Submodule.span_le.mpr
  rintro _ ⟨v,rfl⟩
  refine ⟨SymmetricPower.tprod ℂ
    ![exteriorPower.ιMulti ℂ 2 ![v 0,v 1], exteriorPower.ιMulti ℂ 2 ![v 2,v 3]], ?_⟩
  change wedgeMap (SymmetricPower.tprod ℂ
    ![exteriorPower.ιMulti ℂ 2 ![v 0,v 1], exteriorPower.ιMulti ℂ 2 ![v 2,v 3]]) = _
  rw [wedge_tprod]
  apply Subtype.ext
  change ExteriorAlgebra.ιMulti ℂ 2 ![v 0,v 1] *
    ExteriorAlgebra.ιMulti ℂ 2 ![v 2,v 3] = ExteriorAlgebra.ιMulti ℂ 4 v
  rw [ExteriorAlgebra.ιMulti_mul_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem kernel_finrank : Module.finrank ℂ kernel.toSubmodule = 50 := by
  have hd := LinearMap.finrank_range_add_finrank_ker wedgeMap.toLinearMap
  rw [LinearMap.range_eq_top.mpr wedge_surjective, finrank_top] at hd
  have hs : Module.finrank ℂ (Sym[ℂ]^2 Ten) = 55 := by
    norm_num [SymmetricPower.finrank_eq, Ten, Five, exteriorPower.finrank_eq,
      Nat.choose, Nat.multichoose] 
  have ht : Module.finrank ℂ Fourth = 5 := by
    norm_num [Fourth, Five, exteriorPower.finrank_eq, Nat.choose]
  rw [hs,ht] at hd
  change Module.finrank ℂ (LinearMap.ker wedgeMap.toLinearMap) = 50
  omega
/-- Actual trace identity from the proved exact sequence, not supplied character data. -/
theorem kernel_character (g : TargetGroup) :
    kernel.toRepresentation.character g = (ten.symmetricPower 2).character g -
      (fundamental.exteriorPower 4).character g := by
  have hh : (ten.symmetricPower 2).character g = kernel.toRepresentation.character g +
      (fundamental.exteriorPower 4).character g := by
    apply Math.CharacterExact.character_eq_add_of_exact
      (Math.CharacterExact.subtypeIntertwiner wedgeMap.ker) wedgeMap
      Subtype.val_injective wedge_surjective
    apply LinearMap.exact_iff.mpr
    change LinearMap.ker wedgeMap.toLinearMap =
      LinearMap.range wedgeMap.ker.toSubmodule.subtype
    rw [Submodule.range_subtype]
    rfl
  exact eq_sub_of_add_eq hh.symm

end
end GUT.SU5.ExoticSymmetricKernel
