import Math.Algebra.Jets.JetEngineeringDegree
import Mathlib.Tactic

/-! Complete engineering-degree-two scalar source: phi squared and first jets. -/
namespace Math.ScalarEngineeringTwo
set_option autoImplicit false
noncomputable section
open ScalarJetAlgebra MvPolynomial
variable {I : Type*}
abbrev J (I : Type*) := ScalarJetAlgebra.Index Unit I
def zeroIndex : J I := ((), 0)
def firstIndex (i : I) : J I := ((), Finsupp.single i 1)

theorem weight_zero (a : J I →₀ ℕ) (h : Finsupp.weight JetEngineering.weight a = 0) : a = 0 := by
  ext j
  by_contra hj
  have hb := Finsupp.le_weight_of_ne_zero' JetEngineering.weight hj
  rw [h] at hb
  dsimp [JetEngineering.weight] at hb
  omega

theorem index_weight_one (j : J I) (h : JetEngineering.weight j = 1) : j = zeroIndex := by
  have hz : j.2 = 0 := by
    ext i
    by_contra hi
    have hb := Finsupp.le_weight_of_ne_zero' (fun _ : I => (1 : ℕ)) hi
    change 1 ≤ order j.2 at hb
    dsimp [JetEngineering.weight] at h
    omega
  rcases j with ⟨⟨⟩, a⟩
  exact Prod.ext rfl hz

theorem exponent_weight_one (a : J I →₀ ℕ) (h : Finsupp.weight JetEngineering.weight a = 1) :
    a = Finsupp.single zeroIndex 1 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
    by_contra! hz
    have ha : a = 0 := by ext j; exact hz j
    simp [ha] at h
  have hw := Finsupp.weight_sub_single_add (w := JetEngineering.weight) hj
  rw [h] at hw
  have hp : 1 ≤ JetEngineering.weight j := by dsimp [JetEngineering.weight]; omega
  have h0 : Finsupp.weight JetEngineering.weight (a - Finsupp.single j 1) = 0 := by omega
  have h1 : JetEngineering.weight j = 1 := by omega
  have he := Finsupp.sub_add_single_one_cancel hj
  rw [weight_zero _ h0, zero_add, index_weight_one j h1] at he
  exact he.symm

theorem index_weight_two (j : J I) (h : JetEngineering.weight j = 2) :
    ∃ i, j = firstIndex i := by
  have ho : order j.2 = 1 := by dsimp [JetEngineering.weight] at h; omega
  have hs : j.2.sum (fun _ n => n) = 1 := by
    simpa [order, Finsupp.weight_apply] using ho
  obtain ⟨i, hi⟩ := (Finsupp.sum_eq_one_iff _).mp hs
  exact ⟨i, Prod.ext (Subsingleton.elim _ _) hi⟩

theorem exponent_weight_two (a : J I →₀ ℕ) (h : Finsupp.weight JetEngineering.weight a = 2) :
    a = Finsupp.single zeroIndex 2 ∨ ∃ i, a = Finsupp.single (firstIndex i) 1 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
    by_contra! hz
    have ha : a = 0 := by ext j; exact hz j
    simp [ha] at h
  have hw := Finsupp.weight_sub_single_add (w := JetEngineering.weight) hj
  rw [h] at hw
  have hp : 1 ≤ JetEngineering.weight j := by dsimp [JetEngineering.weight]; omega
  have hc : JetEngineering.weight j = 1 ∨ JetEngineering.weight j = 2 := by omega
  have he := Finsupp.sub_add_single_one_cancel hj
  rcases hc with h1 | h2
  · left
    have hb : Finsupp.weight JetEngineering.weight (a - Finsupp.single j 1) = 1 := by omega
    rw [exponent_weight_one _ hb, index_weight_one j h1, ← Finsupp.single_add] at he
    exact he.symm
  · right
    have hb : Finsupp.weight JetEngineering.weight (a - Finsupp.single j 1) = 0 := by omega
    obtain ⟨i, hi⟩ := index_weight_two j h2
    rw [weight_zero _ hb, zero_add, hi] at he
    exact ⟨i, he.symm⟩

abbrev Source (I : Type*) := JetEngineering.grade Unit I 2

def square : Source I := ⟨monomial (Finsupp.single zeroIndex 2) 1,
  MvPolynomial.isWeightedHomogeneous_monomial JetEngineering.weight _ _ (by
    simp [JetEngineering.weight, zeroIndex, order, Finsupp.weight_single])⟩

def first (i : I) : Source I := ⟨X (firstIndex i), by
  simpa [JetEngineering.grade, JetEngineering.weight, firstIndex, order, Finsupp.weight_single] using
    MvPolynomial.isWeightedHomogeneous_X ℂ JetEngineering.weight (firstIndex i)⟩

theorem source_reconstruct [Fintype I] (p : Source I) :
    p = p.val.coeff (Finsupp.single zeroIndex 2) • square +
      ∑ i, p.val.coeff (Finsupp.single (firstIndex i) 1) • first i := by
  classical
  apply Subtype.ext
  apply MvPolynomial.ext
  intro a
  have hz (i : I) : (Finsupp.single (zeroIndex : J I) 2) ≠ Finsupp.single (firstIndex i) 1 := by
    intro h
    have he := congrArg (fun b : J I →₀ ℕ => b zeroIndex) h
    simp [zeroIndex, firstIndex] at he
  have hzs (i : I) := Ne.symm (hz i)
  have hf : Function.Injective (fun i : I => Finsupp.single (firstIndex i) 1) := by
    intro i j h
    have hi := Finsupp.single_left_injective (show (1 : ℕ) ≠ 0 by decide) h
    exact Finsupp.single_left_injective (show (1 : ℕ) ≠ 0 by decide) (congrArg Prod.snd hi)
  by_cases ha : a = Finsupp.single zeroIndex 2
  · subst a
    simp [square, first, X, hzs]
  · by_cases hb : ∃ i, a = Finsupp.single (firstIndex i) 1
    · obtain ⟨i, rfl⟩ := hb
      simp [square, first, X, hz, hf.eq_iff]
    · have hc : p.val.coeff a = 0 := by
        by_contra hc
        exact (exponent_weight_two a (p.property hc)).elim ha hb
      simp [square, first, X, coeff_monomial, hc, Ne.symm ha,
        show ∀ i, Finsupp.single (firstIndex i) 1 ≠ a from fun i h => hb ⟨i, h.symm⟩]

end
end Math.ScalarEngineeringTwo
