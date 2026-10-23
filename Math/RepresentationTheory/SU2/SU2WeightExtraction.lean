import TauCeti.RepresentationTheory.SU2.Weyl.Integration
import Math.RepresentationTheory.Characters.CompactHomDimension

/-! A structural A1 multiplicity functional on finite symmetric weight
expansions. No enumeration of representation degrees is used. -/
namespace Math.SU2WeightExtraction
set_option autoImplicit false
noncomputable section
open TauCeti TauCeti.SU2 MeasureTheory
open scoped BigOperators

def pairCharacter : ℕ → SU2 → ℂ
  | 0 => (symPower 0).character
  | 1 => (symPower 1).character
  | n+2 => (symPower (n+2)).character - (symPower n).character

def pairWeight : ℕ → Circle → ℂ
  | 0, _ => 1
  | n+1, z => (z : ℂ)^(n+1) + ((z : ℂ)⁻¹)^(n+1)

theorem pairCharacter_torus (k : ℕ) (z : Circle) :
    pairCharacter k (torusHom z) = pairWeight k z := by
  cases k with
  | zero => simp [pairCharacter, pairWeight, character_symPower_torusHom]
  | succ k =>
    cases k with
    | zero => simp [pairCharacter, pairWeight, character_symPower_torusHom,
        Finset.sum_range_succ, add_comm]
    | succ k =>
      simp only [pairCharacter, Pi.sub_apply, character_symPower_torusHom_zpow]
      rw [Finset.sum_range_succ, Finset.sum_range_succ']
      have hm : (∑ i ∈ Finset.range (k+1),
          (z : ℂ) ^ (2 * ((i+1 : ℕ) : ℤ) - (k+2 : ℕ))) =
          ∑ i ∈ Finset.range (k+1), (z : ℂ) ^ (2 * (i : ℤ) - k) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        push_cast
        ring
      rw [hm]
      have ht : 2 * ((k+2 : ℕ) : ℤ) - (k+2 : ℕ) = (k+2 : ℕ) := by omega
      simp only [ht, Nat.cast_zero, mul_zero, zero_sub, zpow_neg, zpow_natCast]
      simp only [pairWeight, inv_pow]
      ring

theorem pairCharacter_conj (k : ℕ) (u g : SU2) :
    pairCharacter k (u*g*u⁻¹) = pairCharacter k g := by
  cases k with
  | zero => exact Representation.char_conj _ _ _
  | succ k =>
    cases k <;> simp [pairCharacter, Representation.char_conj]

theorem continuous_pairCharacter (k : ℕ) : Continuous (pairCharacter k) := by
  cases k with
  | zero => exact continuous_character_symPower 0
  | succ k =>
    cases k with
    | zero => exact continuous_character_symPower 1
    | succ k =>
      exact (continuous_character_symPower (k+2)).sub (continuous_character_symPower k)

theorem integrable_pairCharacter (k : ℕ) :
    Integrable (pairCharacter k) (haarProb SU2) :=
  (continuous_pairCharacter k).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integral_pairCharacter (k : ℕ) :
    (∫ g, pairCharacter k g ∂haarProb SU2) =
      (if k=0 then 1 else 0) - (if k=2 then 1 else 0) := by
  cases k with
  | zero => simp only [pairCharacter, integral_character_symPower]; norm_num
  | succ k =>
    cases k with
    | zero => simp only [pairCharacter, integral_character_symPower]; norm_num
    | succ k =>
      rw [show pairCharacter (k+1+1) =
        (symPower (k+2)).character - (symPower k).character from rfl]
      simp only [Pi.sub_apply]
      rw [integral_sub
          ((continuous_character_symPower (k+2)).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))
          ((continuous_character_symPower k).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))]
      simp [integral_character_symPower]

/-- Extract the trivial multiplicity functional from any finite symmetric
weight expansion: the coefficients at weights zero and two suffice. -/
theorem integral_of_weight_expansion (f : SU2 → ℂ) (c : ℕ →₀ ℂ)
    (hc : ∀ u g, f (u*g*u⁻¹) = f g)
    (ht : ∀ z, f (torusHom z) = c.sum (fun k a => a * pairWeight k z)) :
    (∫ g, f g ∂haarProb SU2) = c 0 - c 2 := by
  classical
  have he : f = fun g => ∑ k ∈ c.support, c k * pairCharacter k g := by
    apply eq_of_conjInvariant_of_eqOn_torus hc
    · intro u g
      simp only [pairCharacter_conj]
    · intro g hg
      obtain ⟨z, rfl⟩ := mem_torus_iff_exists_torusHom.mp hg
      simpa only [Finsupp.sum, pairCharacter_torus] using ht z
  rw [he, integral_finsetSum]
  · simp_rw [integral_const_mul, integral_pairCharacter, mul_sub]
    rw [Finset.sum_sub_distrib]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finsupp.mem_support_iff]
    split_ifs <;> simp_all
  · intro k hk
    exact (integrable_pairCharacter k).const_mul (c k)

/-- For a continuous finite-dimensional representation, the extracted scalar
is the dimension of its invariant vectors, not just a formal coefficient. -/
theorem invariant_finrank {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (rho : Representation ℂ SU2 V)
    (hr : ContinuousRepresentationScope.IsJointlyContinuous rho)
    (c : ℕ →₀ ℂ)
    (ht : ∀ z, rho.character (torusHom z) = c.sum (fun k a => a * pairWeight k z)) :
    (Module.finrank ℂ (Representation.IntertwiningMap
      (Representation.trivial ℂ SU2 ℂ) rho) : ℂ) = c 0 - c 2 := by
  have h := CompactHomDimension.integral_character_mul_eq_finrank
    (Representation.trivial ℂ SU2 ℂ) rho (by exact continuous_snd) hr
  have he := integral_of_weight_expansion rho.character c
    (fun u g => Representation.char_conj rho g u) ht
  have hi : (∫ g, rho.character g ∂haarProb SU2) =
      (Module.finrank ℂ (Representation.IntertwiningMap
        (Representation.trivial ℂ SU2 ℂ) rho) : ℂ) := by
    simpa using h
  exact hi.symm.trans he

/-- A1 × A1 extraction, with the two group variables kept independent. -/
theorem integral_pair_of_weight_expansion (f : SU2 → SU2 → ℂ)
    (c : ℕ × ℕ →₀ ℂ)
    (hleft : ∀ u g h, f (u*g*u⁻¹) h = f g h)
    (hright : ∀ u g h, f g (u*h*u⁻¹) = f g h)
    (ht : ∀ z w, f (torusHom z) (torusHom w) =
      c.sum (fun k a => a * pairWeight k.1 z * pairWeight k.2 w)) :
    (∫ g, ∫ h, f g h ∂haarProb SU2 ∂haarProb SU2) =
      c (0,0) - c (0,2) - c (2,0) + c (2,2) := by
  classical
  have he : ∀ g h, f g h =
      ∑ k ∈ c.support, c k * pairCharacter k.1 g * pairCharacter k.2 h := by
    have hg : ∀ w, (fun g => f g (torusHom w)) =
        fun g => ∑ k ∈ c.support, c k * pairCharacter k.1 g * pairWeight k.2 w := by
      intro w
      apply eq_of_conjInvariant_of_eqOn_torus (fun u g => hleft u g _)
      · intro u g; simp only [pairCharacter_conj]
      · intro g hm
        obtain ⟨z, rfl⟩ := mem_torus_iff_exists_torusHom.mp hm
        simpa only [Finsupp.sum, pairCharacter_torus] using ht z w
    intro g
    have hh : (fun h => f g h) =
        fun h => ∑ k ∈ c.support, c k * pairCharacter k.1 g * pairCharacter k.2 h := by
      apply eq_of_conjInvariant_of_eqOn_torus (fun u h => hright u g h)
      · intro u h; simp only [pairCharacter_conj]
      · intro h hm
        obtain ⟨w, rfl⟩ := mem_torus_iff_exists_torusHom.mp hm
        simpa only [pairCharacter_torus] using congrFun (hg w) g
    exact congrFun hh
  simp_rw [he]
  have hi (g : SU2) :
      (∫ h, ∑ k ∈ c.support, c k * pairCharacter k.1 g * pairCharacter k.2 h
        ∂haarProb SU2) =
      ∑ k ∈ c.support, c k * pairCharacter k.1 g *
        ((if k.2=0 then 1 else 0) - (if k.2=2 then 1 else 0)) := by
    rw [integral_finsetSum]
    · simp_rw [integral_const_mul, integral_pairCharacter]
    · intro k hk; exact (integrable_pairCharacter k.2).const_mul _
  simp_rw [hi]
  rw [integral_finsetSum]
  · simp_rw [integral_mul_const, integral_const_mul, integral_pairCharacter]
    have hterm (k : ℕ × ℕ) :
        c k * ((if k.1=0 then 1 else 0) - (if k.1=2 then 1 else 0)) *
          ((if k.2=0 then 1 else 0) - (if k.2=2 then 1 else 0)) =
        (if k=(0,0) then c k else 0) - (if k=(0,2) then c k else 0) -
          (if k=(2,0) then c k else 0) + (if k=(2,2) then c k else 0) := by
      rcases k with ⟨a,b⟩
      simp only [Prod.mk.injEq]
      by_cases ha : a=0 <;> by_cases ha2 : a=2 <;>
        by_cases hb : b=0 <;> by_cases hb2 : b=2 <;> simp [ha, ha2, hb, hb2]
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hs (j : ℕ × ℕ) :
        (∑ k ∈ c.support, if k=j then c k else 0) = c j := by
      rw [Finset.sum_ite_eq']
      split_ifs with hj
      · rfl
      · exact (Finsupp.notMem_support_iff.mp hj).symm
    rw [hs, hs, hs, hs]
  · intro k hk
    exact ((integrable_pairCharacter k.1).const_mul _).mul_const _

end
end Math.SU2WeightExtraction
