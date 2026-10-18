import Math.RepresentationTheory.FourSlotAlternation

/-! Alternation for species pattern (A,A,A,B). The normalization on the
ordered probe is 3!, not the factor 2 of pattern (A,A,B,C). -/
namespace Math.FourSlotTripleAlternation
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {H A B : Type*} [Group H] [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]

abbrev Tensor := (A ⊗[ℂ] A) ⊗[ℂ] (A ⊗[ℂ] B)

def ordered (f : Tensor (A := A) (B := B) →ₗ[ℂ] ℂ) :
    MultilinearMap ℂ (fun _ : Fin 4 => A × B) ℂ :=
  MultilinearMap.mk' (fun v => f (((v 0).1 ⊗ₜ[ℂ] (v 1).1) ⊗ₜ[ℂ]
    ((v 2).1 ⊗ₜ[ℂ] (v 3).2)))
    (by intro v i x y; fin_cases i <;>
      simp [Function.update, TensorProduct.add_tmul, TensorProduct.tmul_add])
    (by intro v i c x; fin_cases i <;>
      simp [Function.update, TensorProduct.smul_tmul, TensorProduct.tmul_smul])

def alternating (f : Tensor (A := A) (B := B) →ₗ[ℂ] ℂ) :
    (A × B) [⋀^Fin 4]→ₗ[ℂ] ℂ := (ordered f).alternatization

def slots (x y z : A) (h : B) : Fin 4 → A × B := ![(x,0), (y,0), (z,0), (0,h)]

/-- Permutation form of first-three-slot alternation. -/
def Alternates (f : Tensor (A := A) (B := B) →ₗ[ℂ] ℂ) : Prop :=
  ∀ (p : Equiv.Perm (Fin 4)), p 3 = 3 → ∀ x y z h,
    ordered f (slots x y z h ∘ p) = Equiv.Perm.sign p • f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h))

theorem alternating_slots (f : Tensor (A := A) (B := B) →ₗ[ℂ] ℂ)
    (hf : Alternates f) (x y z : A) (h : B) :
    alternating f (slots x y z h) = (6 : ℂ) * f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h)) := by
  classical
  have hn (i : Fin 4) (hi : i ≠ 3) : (slots x y z h i).2 = 0 := by
    fin_cases i <;> simp_all [slots]
  have hc : (Finset.univ.filter (fun p : Equiv.Perm (Fin 4) => p 3 = 3)).card = 6 := by
    decide +kernel
  rw [alternating, MultilinearMap.alternatization_apply]
  calc
    _ = ∑ p : Equiv.Perm (Fin 4), if p 3 = 3 then
        f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h)) else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p 3 = 3
      · simp only [MultilinearMap.domDomCongr_apply, hp, ↓reduceIte]
        change Equiv.Perm.sign p • ordered f (slots x y z h ∘ p) = _
        rw [hf p hp, smul_smul, Int.units_mul_self, one_smul]
      · simp [hp, MultilinearMap.domDomCongr_apply, ordered, hn _ hp]
    _ = _ := by rw [← Finset.sum_filter]; simp [hc, nsmul_eq_mul]

variable (a : Representation ℂ H A) (b : Representation ℂ H B)

def coefficient (f : IntertwiningMap ((a.tprod a).tprod (a.tprod b))
    (Representation.trivial ℂ H ℂ)) :
    IntertwiningMap ((a.prod b).exteriorPower 4) (Representation.trivial ℂ H ℂ) where
  toLinearMap := exteriorPower.alternatingMapLinearEquiv (alternating f.toLinearMap)
  isIntertwining' g := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Representation.exteriorPower_apply_ιMulti,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      alternating, MultilinearMap.alternatization_apply, Representation.trivial_apply]
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    change f (((a.tprod a).tprod (a.tprod b)) g
      (((v (p 0)).1 ⊗ₜ[ℂ] (v (p 1)).1) ⊗ₜ[ℂ] ((v (p 2)).1 ⊗ₜ[ℂ] (v (p 3)).2))) = _
    exact IntertwiningMap.isIntertwining _ _ f g _

theorem coefficient_slots (f : IntertwiningMap ((a.tprod a).tprod (a.tprod b))
    (Representation.trivial ℂ H ℂ)) (hf : Alternates f.toLinearMap) (x y z : A) (h : B) :
    coefficient a b f (exteriorPower.ιMulti ℂ 4 (slots x y z h)) =
      (6 : ℂ) * f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h)) := by
  change exteriorPower.alternatingMapLinearEquiv _ _ = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact alternating_slots _ hf x y z h

end
end Math.FourSlotTripleAlternation
