import Math.RepresentationTheory.FiniteSpeciesProjection

/-! Normalized extension of an ordered species pattern to the full field sum.
Only permutations preserving the pattern contribute to its ordered restriction. -/
namespace Math.SpeciesPatternAssembly
set_option autoImplicit false
noncomputable section
open Representation FiniteSpeciesExterior
variable {S G : Type*} [Fintype S] [DecidableEq S] [Group G]
  {V : S → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  (r : ∀ s, Representation ℂ G (V s)) (pattern : Fin 4 → S)

def ordered (k : MultilinearMap ℂ (fun i => V (pattern i)) ℂ) :
    MultilinearMap ℂ (fun _ : Fin 4 => ∀ s, V s) ℂ :=
  k.compLinearMap (fun i => LinearMap.proj (pattern i))

def stabilizer : Finset (Equiv.Perm (Fin 4)) := Finset.univ.filter (fun p => pattern ∘ p = pattern)

def Compatible (k : MultilinearMap ℂ (fun i => V (pattern i)) ℂ) : Prop :=
  ∀ (p : Equiv.Perm (Fin 4)), pattern ∘ p = pattern → ∀ w : Fin 4 → ∀ s, V s,
    Equiv.Perm.sign p • ordered pattern k (w ∘ p) = ordered pattern k w

def alternating (k : MultilinearMap ℂ (fun i => V (pattern i)) ℂ) :
    (∀ s, V s) [⋀^Fin 4]→ₗ[ℂ] ℂ :=
  ((stabilizer pattern).card : ℂ)⁻¹ • (ordered pattern k).alternatization

omit [Fintype S] in
theorem stabilizer_ne_zero : ((stabilizer pattern).card : ℂ) ≠ 0 := by
  have hm : (1 : Equiv.Perm (Fin 4)) ∈ stabilizer pattern := by simp [stabilizer]
  exact_mod_cast (Finset.card_ne_zero.mpr ⟨1,hm⟩)

omit [Fintype S] in
theorem alternating_pure (k : MultilinearMap ℂ (fun i => V (pattern i)) ℂ)
    (hk : Compatible pattern k) (v : ∀ i, V (pattern i)) :
    alternating pattern k (fun i => Pi.single (pattern i) (v i)) = k v := by
  classical
  let w : Fin 4 → ∀ s, V s := fun i => Pi.single (pattern i) (v i)
  have ho : ordered pattern k w = k v := by simp [ordered,w]
  have ht (p : Equiv.Perm (Fin 4)) :
      Equiv.Perm.sign p • ordered pattern k (w ∘ p) =
        if pattern ∘ p = pattern then k v else 0 := by
    by_cases hp : pattern ∘ p = pattern
    · rw [ite_eq_left hp, hk p hp, ho]
    · rw [ite_eq_right hp]
      obtain ⟨i,hi⟩ : ∃ i, pattern (p i) ≠ pattern i := by
        by_contra hn
        exact hp (funext (fun i => by simpa using not_exists.mp hn i))
      have hz : ordered pattern k (w ∘ p) = 0 := by
        apply k.map_coord_zero i
        exact Pi.single_eq_of_ne (Ne.symm hi) _
      rw [hz, smul_zero]
  simp only [alternating, AlternatingMap.smul_apply, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply]
  change ((stabilizer pattern).card : ℂ)⁻¹ •
    (∑ p, Equiv.Perm.sign p • ordered pattern k (w ∘ p)) = _
  simp_rw [ht]
  rw [← Finset.sum_filter]
  change ((stabilizer pattern).card : ℂ)⁻¹ • (∑ _p ∈ stabilizer pattern, k v) = _
  simp only [Finset.sum_const, nsmul_eq_mul, smul_eq_mul]
  exact inv_mul_cancel_left₀ (stabilizer_ne_zero pattern) _

omit [Fintype S] in
theorem alternating_vanish (k : MultilinearMap ℂ (fun i => V (pattern i)) ℂ)
    (labels : Fin 4 → S) (v : ∀ i, V (labels i))
    (h : ¬ ∃ p : Equiv.Perm (Fin 4), labels ∘ p = pattern) :
    alternating pattern k (fun i => Pi.single (labels i) (v i)) = 0 := by
  simp only [alternating, AlternatingMap.smul_apply, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply]
  suffices hz : (∑ p : Equiv.Perm (Fin 4), Equiv.Perm.sign p •
      ordered pattern k (fun i => Pi.single (labels (p i)) (v (p i)))) = 0 by
    rw [hz, smul_zero]
  apply Finset.sum_eq_zero
  intro p _
  obtain ⟨i,hi⟩ : ∃ i, labels (p i) ≠ pattern i := by
    by_contra hn
    exact h ⟨p,funext (fun i => by simpa using not_exists.mp hn i)⟩
  have hz : ordered pattern k (fun i => Pi.single (labels (p i)) (v (p i))) = 0 := by
    apply k.map_coord_zero i
    exact Pi.single_eq_of_ne (Ne.symm hi) _
  rw [hz, smul_zero]

def assemble (k : MultilinearInvariantHom.invariantMaps (W := ℂ) (fun i => r (pattern i))) :
    Coefficient r 4 where
  toLinearMap := exteriorPower.alternatingMapLinearEquiv (alternating pattern k.val)
  isIntertwining' g := by
    apply exteriorPower.linearMap_ext
    ext w
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Representation.exteriorPower_apply_ιMulti,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, alternating,
      AlternatingMap.smul_apply, MultilinearMap.alternatization_apply,
      MultilinearMap.domDomCongr_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    exact congrArg (Equiv.Perm.sign p • ·) (k.property g (fun i => w (p i) (pattern i)))

theorem restrict_assemble (k : MultilinearInvariantHom.invariantMaps (W := ℂ) (fun i => r (pattern i)))
    (hk : Compatible pattern k.val) : restrict r (assemble r pattern k) pattern = k.val := by
  ext v
  rw [restrict_apply]
  change exteriorPower.alternatingMapLinearEquiv (alternating pattern k.val) _ = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact alternating_pure pattern k.val hk v

def orderedSpace : Submodule ℂ
    (MultilinearInvariantHom.invariantMaps (W := ℂ) (fun i => r (pattern i))) where
  carrier := {k | Compatible pattern k.val}
  zero_mem' := by intro p hp w; simp [ordered]
  add_mem' := by
    intro k l hk hl p hp w
    change Equiv.Perm.sign p • (ordered pattern k.val (w ∘ p) +
      ordered pattern l.val (w ∘ p)) = ordered pattern k.val w + ordered pattern l.val w
    rw [smul_add, hk p hp, hl p hp]
  smul_mem' := by
    intro z k hk p hp w
    change Equiv.Perm.sign p • (z • ordered pattern k.val (w ∘ p)) = z • ordered pattern k.val w
    rw [smul_comm, hk p hp]

def restriction (f : Coefficient r 4) : orderedSpace r pattern :=
  ⟨⟨restrict r f pattern, restrict_invariant r f pattern⟩, by
    intro p hp w
    let v : Fin 4 → ∀ s, V s := fun i => Pi.single (pattern i) (w i (pattern i))
    have he := (evaluation r f).map_congr_perm v p
    have hv : v ∘ p = fun i => Pi.single (pattern i) (w (p i) (pattern i)) := by
      funext i
      have hi := congrFun hp i
      dsimp only [Function.comp_apply] at hi
      simp only [v, Function.comp_apply]
      rw [hi]
    rw [hv] at he
    exact he.symm⟩

variable (P : (Fin 4 → S) → Prop) [DecidablePred P]
  (stable : ∀ labels (p : Equiv.Perm (Fin 4)), P (labels ∘ p) ↔ P labels)
  (orbit : ∀ labels, P labels → ∃ p : Equiv.Perm (Fin 4), labels ∘ p = pattern)
  (member : P pattern)

def extension (k : orderedSpace r pattern) : FiniteSpeciesProjection.supportSpace r P :=
  ⟨assemble r pattern k.val, by
    intro labels hn
    ext v
    rw [restrict_apply]
    change exteriorPower.alternatingMapLinearEquiv (alternating pattern k.val.val) _ = _
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    apply alternating_vanish pattern k.val.val labels v
    rintro ⟨p,hp⟩
    exact hn ((stable labels p).mp (hp.symm ▸ member))⟩

def equiv : FiniteSpeciesProjection.supportSpace r P ≃ₗ[ℂ] orderedSpace r pattern where
  toFun f := restriction r pattern f.val
  invFun := extension r pattern P stable member
  left_inv f := by
    apply FiniteSpeciesProjection.pattern_ext r P pattern orbit
    exact restrict_assemble r pattern _ (restriction r pattern f.val).property
  right_inv k := by
    apply Subtype.ext
    apply Subtype.ext
    exact restrict_assemble r pattern k.val k.property
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    exact restrict_add r f.val g.val pattern
  map_smul' z f := by
    apply Subtype.ext
    apply Subtype.ext
    exact restrict_smul r z f.val pattern

end
end Math.SpeciesPatternAssembly
