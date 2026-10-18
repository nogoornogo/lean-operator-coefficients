import GUT.SU5.Representations.ExoticWedgeKernel

namespace GUT.SU5.WedgeKernelProjection
set_option autoImplicit false
noncomputable section
open Matter Representation ExoticWedgeKernel
open scoped TensorProduct

private theorem permutations_three : (Finset.univ : Finset (Equiv.Perm (Fin 3))) =
    {1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
      Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 0 1} := by
  decide

def pair (x y : Five) : Ten := exteriorPower.ιMulti ℂ 2 ![x,y]

theorem pair_add_left (x y z : Five) : pair (x+y) z = pair x z + pair y z := by
  exact (exteriorPower.ιMulti ℂ 2).map_vecCons_add _ _ _
theorem pair_smul_left (c : ℂ) (x y : Five) : pair (c • x) y = c • pair x y := by
  exact (exteriorPower.ιMulti ℂ 2).map_vecCons_smul _ _ _
theorem pair_add_right (x y z : Five) : pair x (y+z) = pair x y + pair x z := by
  have h := (exteriorPower.ιMulti ℂ 2).map_update_add ![x,y] 1 y z
  convert h using 1 <;> congr 1
theorem pair_smul_right (c : ℂ) (x y : Five) : pair x (c • y) = c • pair x y := by
  have h := (exteriorPower.ιMulti ℂ 2).map_update_smul ![x,y] 1 c y
  convert h using 1 <;> congr 1

theorem pair_swap (x y : Five) : pair y x = -pair x y := by
  have h := (exteriorPower.ιMulti ℂ 2).map_swap ![x,y] (by decide : (0 : Fin 2) ≠ 1)
  have he : ![x,y] ∘ Equiv.swap 0 1 = ![y,x] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at h
  exact h

def raw : MultilinearMap ℂ (fun _ : Fin 3 => Five) (Five ⊗[ℂ] Ten) where
  toFun v := v 0 ⊗ₜ[ℂ] pair (v 1) (v 2)
  map_update_add' v i x y := by
    fin_cases i <;>
      simp only [Function.update_apply, Fin.ext_iff] <;>
      norm_num [pair_add_left, pair_add_right, TensorProduct.add_tmul,
        TensorProduct.tmul_add]
  map_update_smul' v i c x := by
    fin_cases i <;>
      simp only [Function.update_apply, Fin.ext_iff] <;>
      norm_num [pair_smul_left, pair_smul_right, TensorProduct.smul_tmul',
        TensorProduct.tmul_smul]

def sectionLinear : Cube →ₗ[ℂ] Five ⊗[ℂ] Ten :=
  (1/6 : ℂ) • exteriorPower.alternatingMapLinearEquiv raw.alternatization

theorem section_pure (x y z : Five) :
    sectionLinear (exteriorPower.ιMulti ℂ 3 ![x,y,z]) = (1/3 : ℂ) •
      (x ⊗ₜ[ℂ] pair y z + y ⊗ₜ[ℂ] pair z x + z ⊗ₜ[ℂ] pair x y) := by
  simp only [sectionLinear, LinearMap.smul_apply,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    MultilinearMap.alternatization_apply, permutations_three]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have hr (v : Fin 3 → Five) : raw v = v 0 ⊗ₜ[ℂ] pair (v 1) (v 2) := rfl
  simp only [MultilinearMap.domDomCongr_apply, hr]
  norm_num [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap, Equiv.swap_apply_def,
    Fin.ext_iff, Equiv.Perm.mul_apply]
  rw [pair_swap z y, pair_swap x z, pair_swap y x]
  simp only [TensorProduct.tmul_neg, smul_neg]
  module

theorem wedge_raw : wedgeLinear.compMultilinearMap raw =
    (exteriorPower.ιMulti ℂ 3).toMultilinearMap := by
  ext v
  simp only [LinearMap.compMultilinearMap_apply, raw, MultilinearMap.coe_mk,
    pair, wedge_tmul]
  have he : ![v 0, v 1, v 2] = v := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  rfl

theorem wedge_section : wedgeLinear.comp sectionLinear = LinearMap.id := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change wedgeLinear ((1/6 : ℂ) •
    exteriorPower.alternatingMapLinearEquiv raw.alternatization
      (exteriorPower.ιMulti ℂ 3 v)) = exteriorPower.ιMulti ℂ 3 v
  rw [map_smul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    ← LinearMap.compAlternatingMap_apply,
    ← LinearMap.compMultilinearMap_alternatization, wedge_raw,
    AlternatingMap.coe_alternatization]
  change (1/6 : ℂ) • ((6 : ℂ) • exteriorPower.ιMulti ℂ 3 v) = exteriorPower.ιMulti ℂ 3 v
  rw [smul_smul]
  norm_num

theorem raw_action (g : StandardModelEmbedding.TargetGroup) :
    (fundamental.tprod ten g).compMultilinearMap raw =
      raw.compLinearMap (fun _ => fundamental g) := by
  ext v
  change (fundamental.tprod ten) g (v 0 ⊗ₜ[ℂ] pair (v 1) (v 2)) =
    fundamental g (v 0) ⊗ₜ[ℂ] pair (fundamental g (v 1)) (fundamental g (v 2))
  rw [Representation.tprod_apply, TensorProduct.map_tmul]
  congr 1
  change (fundamental.exteriorPower 2) g (exteriorPower.ιMulti ℂ 2 ![v 1,v 2]) = _
  rw [Representation.exteriorPower_apply_ιMulti]
  rfl

def sectionMap : IntertwiningMap (fundamental.exteriorPower 3) (fundamental.tprod ten) where
  toLinearMap := sectionLinear
  isIntertwining' g := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    have h := congrArg MultilinearMap.alternatization (raw_action g)
    rw [LinearMap.compMultilinearMap_alternatization,
      MultilinearMap.alternatization_compLinearMap] at h
    have hv := congrArg (fun a : Five [⋀^Fin 3]→ₗ[ℂ] (Five ⊗[ℂ] Ten) => a v) h
    simp only [LinearMap.compAlternatingMap_apply,
      AlternatingMap.compLinearMap_apply] at hv
    change sectionLinear ((fundamental.exteriorPower 3) g
      (exteriorPower.ιMulti ℂ 3 v)) = (fundamental.tprod ten) g
      (sectionLinear (exteriorPower.ιMulti ℂ 3 v))
    simp only [sectionLinear, LinearMap.smul_apply,
      Representation.exteriorPower_apply_ιMulti,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, map_smul]
    exact congrArg (fun x => (1/6 : ℂ) • x) hv.symm

def projection : IntertwiningMap (fundamental.tprod ten) (fundamental.tprod ten) :=
  IntertwiningMap.id _ - sectionMap.comp wedgeMap

theorem wedge_projection (v : Five ⊗[ℂ] Ten) : wedgeLinear (projection v) = 0 := by
  change wedgeLinear (v - sectionLinear (wedgeLinear v)) = 0
  rw [map_sub]
  have h := LinearMap.congr_fun wedge_section (wedgeLinear v)
  change wedgeLinear (sectionLinear (wedgeLinear v)) = wedgeLinear v at h
  rw [h, sub_self]

theorem projection_on_kernel (v : kernel.toSubmodule) : projection v = (v : Five ⊗[ℂ] Ten) := by
  change (v : Five ⊗[ℂ] Ten) - sectionLinear (wedgeLinear v) = _
  have hv : wedgeLinear v = 0 := v.property
  rw [hv, map_zero, sub_zero]

end
end GUT.SU5.WedgeKernelProjection
