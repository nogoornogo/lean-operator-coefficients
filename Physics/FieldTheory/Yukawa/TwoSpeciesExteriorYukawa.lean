import Math.RepresentationTheory.ExternalInvariantTensor
import TauCeti.RepresentationTheory.ExteriorPower

/-! Distinct fermion species: a nonzero ordered Yukawa descends to exterior degree two. -/
namespace GUT.TwoSpeciesExteriorYukawa
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {G A B S : Type*} [Group G]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup S] [Module ℂ S]
  (a : Representation ℂ G A) (b : Representation ℂ G B) (s : Representation ℂ G S)
  (f : IntertwiningMap ((a.tprod b).tprod s) (trivial ℂ G ℂ))

def ordered : MultilinearMap ℂ (fun _ : Fin 2 => A × B) (Module.Dual ℂ S) :=
  MultilinearMap.mk'
    (fun v => (TensorProduct.curry f.toLinearMap) ((v 0).1 ⊗ₜ[ℂ] (v 1).2))
    (by intro v i x y; fin_cases i <;> simp [Function.update,TensorProduct.add_tmul,TensorProduct.tmul_add])
    (by intro v i c x; fin_cases i <;> simp [Function.update,TensorProduct.smul_tmul,TensorProduct.tmul_smul])
def alternating := (ordered a b s f).alternatization

def coefficient : IntertwiningMap ((a.prod b).exteriorPower 2) s.dual where
  toLinearMap := exteriorPower.alternatingMapLinearEquiv (alternating a b s f)
  isIntertwining' g := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    apply LinearMap.ext
    intro h
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Representation.exteriorPower_apply_ιMulti,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    simp only [alternating,MultilinearMap.alternatization_apply]
    change (∑ p : Equiv.Perm (Fin 2), Equiv.Perm.sign p •
      (ordered a b s f).domDomCongr p (fun i => (a.prod b) g (v i))) h =
      (∑ p : Equiv.Perm (Fin 2), Equiv.Perm.sign p •
        (ordered a b s f).domDomCongr p v) (s g⁻¹ h)
    simp only [LinearMap.sum_apply,LinearMap.smul_apply]
    apply Finset.sum_congr rfl
    intro p _
    change (Equiv.Perm.sign p : ℤ) • f
        (((a g (v (p 0)).1) ⊗ₜ[ℂ] (b g (v (p 1)).2)) ⊗ₜ[ℂ] h) =
      (Equiv.Perm.sign p : ℤ) • f
        (((v (p 0)).1 ⊗ₜ[ℂ] (v (p 1)).2) ⊗ₜ[ℂ] s g⁻¹ h)
    congr 1
    have he := IntertwiningMap.isIntertwining _ _ f g
      (((v (p 0)).1 ⊗ₜ[ℂ] (v (p 1)).2) ⊗ₜ[ℂ] s g⁻¹ h)
    simpa [Representation.tprod_apply,TensorProduct.map_tmul] using he

theorem slots (x : A) (y : B) (h : S) :
    coefficient a b s f (exteriorPower.ιMulti ℂ 2 ![(x,0),(0,y)]) h =
      f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] h) := by
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1,Equiv.swap 0 1} := by decide +kernel
  have hn : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide +kernel
  simp [coefficient,alternating,exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    MultilinearMap.alternatization_apply,hu,hn,MultilinearMap.domDomCongr_apply,ordered]

theorem nonzero (x : A) (y : B) (h : S)
    (hf : f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] h) ≠ 0) : coefficient a b s f ≠ 0 := by
  intro hz
  have he := slots a b s f x y h
  rw [hz] at he
  exact hf he.symm
end
end GUT.TwoSpeciesExteriorYukawa
