import Math.RepresentationTheory.Content.MixedSpeciesExt

/-! Separating fixed fermion and scalar content support on actual mixed powers.
All expansions remain symbolic; no basis or species-word list is enumerated. -/
namespace Math.MixedSupportSeparation
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {V : P → Type*} [∀ p, AddCommGroup (V p)] [∀ p, Module ℂ (V p)]
  {W : Q → Type*} [∀ q, AddCommGroup (W q)] [∀ q, Module ℂ (W q)]
  {n m : ℕ}
abbrev F := ⋀[ℂ]^n (∀ p, V p)
abbrev B := Sym[ℂ]^m (∀ q, W q)
abbrev Carrier := F (V := V) (n := n) ⊗[ℂ] B (W := W) (m := m)

omit [Fintype P] [DecidableEq P] in
theorem scalar_ext_zero (f : Carrier (V := V) (W := W) (n := n) (m := m) →ₗ[ℂ] ℂ)
    (x : F (V := V) (n := n))
    (hz : ∀ (labels : Fin m → Q) (w : ∀ j, W (labels j)),
      f (x ⊗ₜ[ℂ] SymmetricPower.tprod ℂ (fun j => Pi.single (labels j) (w j)))=0) :
    ∀ y, f (x ⊗ₜ[ℂ] y)=0 := by
  let g := f.comp (TensorProduct.mk ℂ _ _ x)
  have he : g=0 := by
    apply LinearMap.ext_on (SymmetricPower.span_tprod_eq_top ℂ (Fin m) (∀ q, W q))
    rintro _ ⟨w,rfl⟩
    let ev := g.compMultilinearMap (SymmetricPower.tprod ℂ)
    change ev w=0
    calc
      _ = ev (fun j => ∑ s, Pi.single s (w j s)) := by
        simp only [LinearMap.sum_single_apply]
      _ = ∑ labels : Fin m → Q,
          ev (fun j => Pi.single (labels j) (w j (labels j))) := ev.map_sum _
      _ = 0 := Finset.sum_eq_zero (fun labels _ => hz labels _)
  intro y
  exact LinearMap.congr_fun he y

omit [Fintype Q] [DecidableEq Q] in
theorem fermion_ext_zero (f : Carrier (V := V) (W := W) (n := n) (m := m) →ₗ[ℂ] ℂ)
    (y : B (W := W) (m := m))
    (hz : ∀ (labels : Fin n → P) (v : ∀ i, V (labels i)),
      f (exteriorPower.ιMulti ℂ n (fun i => Pi.single (labels i) (v i)) ⊗ₜ[ℂ] y)=0) :
    ∀ x, f (x ⊗ₜ[ℂ] y)=0 := by
  let g := f.comp ((TensorProduct.mk ℂ _ _).flip y)
  have he : g=0 := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    let ev := g.compAlternatingMap (exteriorPower.ιMulti ℂ n)
    change ev v=0
    calc
      _ = ev (fun i => ∑ s, Pi.single s (v i s)) := by
        simp only [LinearMap.sum_single_apply]
      _ = ∑ labels : Fin n → P,
          ev (fun i => Pi.single (labels i) (v i (labels i))) := ev.toMultilinearMap.map_sum _
      _ = 0 := Finset.sum_eq_zero (fun labels _ => hz labels _)
  intro x
  exact LinearMap.congr_fun he x

theorem separated_iff (f : Carrier (V := V) (W := W) (n := n) (m := m) →ₗ[ℂ] ℂ)
    (a : (Fin n → P) → Prop) (b : (Fin m → Q) → Prop) :
    (∀ labels scalars, ¬ (a labels ∧ b scalars) →
      ∀ (v : ∀ i, V (labels i)) (w : ∀ j, W (scalars j)),
        f (exteriorPower.ιMulti ℂ n (fun i => Pi.single (labels i) (v i)) ⊗ₜ[ℂ]
          SymmetricPower.tprod ℂ (fun j => Pi.single (scalars j) (w j)))=0) ↔
    (∀ labels, ¬ a labels → ∀ (v : ∀ i, V (labels i)) y,
      f (exteriorPower.ιMulti ℂ n (fun i => Pi.single (labels i) (v i)) ⊗ₜ[ℂ] y)=0) ∧
    (∀ scalars, ¬ b scalars → ∀ (w : ∀ j, W (scalars j)) x,
      f (x ⊗ₜ[ℂ] SymmetricPower.tprod ℂ (fun j => Pi.single (scalars j) (w j)))=0) := by
  constructor
  · intro h
    constructor
    · intro labels ha v
      exact scalar_ext_zero f _ (fun scalars w => h labels scalars (fun hs => ha hs.1) v w)
    · intro scalars hb w
      exact fermion_ext_zero f _ (fun labels v => h labels scalars (fun hs => hb hs.2) v w)
  · rintro ⟨ha,hb⟩ labels scalars hn v w
    by_cases h : a labels
    · exact hb scalars (fun ht => hn ⟨h,ht⟩) w _
    · exact ha labels h v _

end
end Math.MixedSupportSeparation
