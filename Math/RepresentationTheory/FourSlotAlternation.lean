import Math.RepresentationTheory.ExternalInvariantTensor
import TauCeti.RepresentationTheory.ExteriorPower
import Mathlib.Tactic

/-! Alternating four-slot coefficients with species pattern (A,A,B,C).
The finite product is the direct sum of the three field spaces. -/

namespace Math.FourSlotAlternation
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct

variable {H A B C : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup C] [Module ℂ C]

abbrev Fields (A B C : Type*) := A × (B × C)

def ordered (f : ((A ⊗[ℂ] A) ⊗[ℂ] (B ⊗[ℂ] C)) →ₗ[ℂ] ℂ) :
    MultilinearMap ℂ (fun _ : Fin 4 => Fields A B C) ℂ :=
  MultilinearMap.mk'
    (fun v => f (((v 0).1 ⊗ₜ[ℂ] (v 1).1) ⊗ₜ[ℂ] ((v 2).2.1 ⊗ₜ[ℂ] (v 3).2.2)))
    (by intro v i x y; fin_cases i <;>
      simp [Function.update, TensorProduct.add_tmul, TensorProduct.tmul_add])
    (by intro v i c x; fin_cases i <;>
      simp [Function.update, TensorProduct.smul_tmul, TensorProduct.tmul_smul])

def alternating (f : ((A ⊗[ℂ] A) ⊗[ℂ] (B ⊗[ℂ] C)) →ₗ[ℂ] ℂ) :
    Fields A B C [⋀^Fin 4]→ₗ[ℂ] ℂ := (ordered f).alternatization

def slots (x y : A) (u : B) (e : C) : Fin 4 → Fields A B C :=
  ![(x, 0, 0), (y, 0, 0), (0, u, 0), (0, 0, e)]

private theorem fixed_last_two (s : Equiv.Perm (Fin 4)) (h2 : s 2 = 2) (h3 : s 3 = 3) :
    s = 1 ∨ s = Equiv.swap 0 1 := by
  have h : ∀ s : Equiv.Perm (Fin 4), s 2 = 2 → s 3 = 3 →
      s = 1 ∨ s = Equiv.swap 0 1 := by decide
  exact h s h2 h3

theorem alternating_slots
    (f : ((A ⊗[ℂ] A) ⊗[ℂ] (B ⊗[ℂ] C)) →ₗ[ℂ] ℂ)
    (x y : A) (u : B) (e : C) :
    alternating f (slots x y u e) =
      f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) -
      f ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) := by
  classical
  have hu (i : Fin 4) (hi : i ≠ 2) : (slots x y u e i).2.1 = 0 := by
    fin_cases i <;> simp_all [slots]
  have he (i : Fin 4) (hi : i ≠ 3) : (slots x y u e i).2.2 = 0 := by
    fin_cases i <;> simp_all [slots]
  unfold alternating
  rw [MultilinearMap.alternatization_apply]
  have hs : ({1, Equiv.swap 0 1} : Finset (Equiv.Perm (Fin 4))) ⊆ Finset.univ :=
    Finset.subset_univ _
  rw [← Finset.sum_subset hs (by
    intro s _ hn
    have hn' : s ≠ 1 ∧ s ≠ Equiv.swap 0 1 := by simpa using hn
    by_cases h2 : s 2 = 2
    · have h3 : s 3 ≠ 3 := fun h3 => (fixed_last_two s h2 h3).elim hn'.1 hn'.2
      simp [MultilinearMap.domDomCongr_apply, ordered, he _ h3]
    · simp [MultilinearMap.domDomCongr_apply, ordered, hu _ h2])]
  have hn : (1 : Equiv.Perm (Fin 4)) ≠ Equiv.swap 0 1 := by decide
  have h2 : (Equiv.swap (0 : Fin 4) 1) 2 = 2 := by decide
  have h3 : (Equiv.swap (0 : Fin 4) 1) 3 = 3 := by decide
  rw [Finset.sum_insert (by simpa using hn), Finset.sum_singleton]
  simp [MultilinearMap.domDomCongr_apply, ordered, slots, sub_eq_add_neg, h2, h3]

variable (a : Representation ℂ H A) (b : Representation ℂ H B)
  (c : Representation ℂ H C)

abbrev action := a.prod (b.prod c)

theorem alternating_invariant
    (f : IntertwiningMap ((a.tprod a).tprod (b.tprod c)) (Representation.trivial ℂ H ℂ))
    (g : H) (v : Fin 4 → Fields A B C) :
    alternating f.toLinearMap (fun i => action a b c g (v i)) =
      alternating f.toLinearMap v := by
  simp only [alternating, MultilinearMap.alternatization_apply]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  change f (((a.tprod a).tprod (b.tprod c)) g
    (((v (s 0)).1 ⊗ₜ[ℂ] (v (s 1)).1) ⊗ₜ[ℂ]
      ((v (s 2)).2.1 ⊗ₜ[ℂ] (v (s 3)).2.2))) = _
  exact IntertwiningMap.isIntertwining _ _ f g _

def coefficient
    (f : IntertwiningMap ((a.tprod a).tprod (b.tprod c)) (Representation.trivial ℂ H ℂ)) :
    IntertwiningMap ((action a b c).exteriorPower 4) (Representation.trivial ℂ H ℂ) where
  toLinearMap := exteriorPower.alternatingMapLinearEquiv (alternating f.toLinearMap)
  isIntertwining' g := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Representation.exteriorPower_apply_ιMulti,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    exact alternating_invariant a b c f g v

theorem coefficient_slots
    (f : IntertwiningMap ((a.tprod a).tprod (b.tprod c)) (Representation.trivial ℂ H ℂ))
    (x y : A) (u : B) (e : C) :
    coefficient a b c f (exteriorPower.ιMulti ℂ 4 (slots x y u e)) =
      f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) -
      f ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) := by
  change exteriorPower.alternatingMapLinearEquiv _ _ = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact alternating_slots _ x y u e

theorem coefficient_ne_zero
    (f : IntertwiningMap ((a.tprod a).tprod (b.tprod c)) (Representation.trivial ℂ H ℂ))
    (x y : A) (u : B) (e : C)
    (hv : f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) -
      f ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) ≠ 0) :
    coefficient a b c f ≠ 0 := by
  intro hz
  have he := coefficient_slots a b c f x y u e
  rw [hz] at he
  exact hv he.symm

/-- Species-preserving transport commutes with alternating descent. -/
theorem coefficient_transport
    {A' B' C' : Type*} [AddCommGroup A'] [Module ℂ A']
    [AddCommGroup B'] [Module ℂ B'] [AddCommGroup C'] [Module ℂ C']
    {a' : Representation ℂ H A'} {b' : Representation ℂ H B'}
    {c' : Representation ℂ H C'}
    (ea : Representation.Equiv a a') (eb : Representation.Equiv b b')
    (ec : Representation.Equiv c c')
    (f : IntertwiningMap ((a'.tprod a').tprod (b'.tprod c'))
      (Representation.trivial ℂ H ℂ)) :
    coefficient a b c (f.comp (ExternalInvariantTensor.tensorEquiv
      (ExternalInvariantTensor.tensorEquiv ea ea)
      (ExternalInvariantTensor.tensorEquiv eb ec)).toIntertwiningMap) =
    (coefficient a' b' c' f).comp
      ((SplitRepresentationProjection.prodEquiv ea
        (SplitRepresentationProjection.prodEquiv eb ec)).exteriorPower 4).toIntertwiningMap := by
  apply IntertwiningMap.ext
  apply exteriorPower.linearMap_ext
  ext v
  simp only [LinearMap.compAlternatingMap_apply, coefficient,
    IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply,
    Representation.Equiv.exteriorPower_toLinearMap,
    exteriorPower.map_apply_ιMulti,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change alternating _ v = alternating f.toLinearMap
    ((SplitRepresentationProjection.prodEquiv ea
      (SplitRepresentationProjection.prodEquiv eb ec)) ∘ v)
  simp only [alternating, MultilinearMap.alternatization_apply]
  apply Finset.sum_congr rfl
  intro s _
  congr 1

theorem coefficient_transport_ne_zero
    {A' B' C' : Type*} [AddCommGroup A'] [Module ℂ A']
    [AddCommGroup B'] [Module ℂ B'] [AddCommGroup C'] [Module ℂ C']
    {a' : Representation ℂ H A'} {b' : Representation ℂ H B'}
    {c' : Representation ℂ H C'}
    (ea : Representation.Equiv a a') (eb : Representation.Equiv b b')
    (ec : Representation.Equiv c c')
    (f : IntertwiningMap ((a'.tprod a').tprod (b'.tprod c'))
      (Representation.trivial ℂ H ℂ)) (hf : coefficient a' b' c' f ≠ 0) :
    coefficient a b c (f.comp (ExternalInvariantTensor.tensorEquiv
      (ExternalInvariantTensor.tensorEquiv ea ea)
      (ExternalInvariantTensor.tensorEquiv eb ec)).toIntertwiningMap) ≠ 0 := by
  rw [coefficient_transport]
  exact ExternalInvariantTensor.comp_equiv_ne_zero _ hf _

end
end Math.FourSlotAlternation
