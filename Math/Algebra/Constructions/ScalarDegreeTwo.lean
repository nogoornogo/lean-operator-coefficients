import Math.Algebra.Constructions.ScalarZeroDerivative

/-! Complete unbounded quartic scalar monomials with two derivatives.
No equation, symmetry or candidate-span hypothesis is assumed. -/
namespace Math.ScalarDegreeTwo
set_option autoImplicit false
noncomputable section
open ScalarJetAlgebra MvPolynomial
variable {I : Type*}
abbrev J (I : Type*) := Index Unit I

theorem order_zero {a : I →₀ ℕ} (ha : order a = 0) : a = 0 := by
  apply Finsupp.ext
  intro i
  change a i = 0
  have hi := Finsupp.le_weight (fun _ : I => 1) (s := i) (by decide) a
  change a i ≤ order a at hi
  omega

theorem order_one {a : I →₀ ℕ} (ha : order a = 1) : ∃ i, a = Finsupp.single i 1 := by
  classical
  have hex : ∃ i, a i ≠ 0 := by
    by_contra h
    push Not at h
    have hz : a = 0 := Finsupp.ext h
    simp [hz,order] at ha
  obtain ⟨i,hi⟩ := hex
  have hw := Finsupp.weight_sub_single_add (w := fun _ : I => (1:ℕ)) hi
  change order (a-Finsupp.single i 1)+1 = order a at hw
  have hz := order_zero (show order (a-Finsupp.single i 1) = 0 by omega)
  refine ⟨i,?_⟩
  have he := Finsupp.sub_add_single_one_cancel hi
  rw [hz,zero_add] at he
  exact he.symm

theorem order_two {a : I →₀ ℕ} (ha : order a = 2) :
    ∃ i j, a = Finsupp.single i 1+Finsupp.single j 1 := by
  classical
  have hex : ∃ i, a i ≠ 0 := by
    by_contra h
    push Not at h
    have hz : a = 0 := Finsupp.ext h
    simp [hz,order] at ha
  obtain ⟨i,hi⟩ := hex
  have hw := Finsupp.weight_sub_single_add (w := fun _ : I => (1:ℕ)) hi
  change order (a-Finsupp.single i 1)+1 = order a at hw
  obtain ⟨j,hj⟩ := order_one (show order (a-Finsupp.single i 1) = 1 by omega)
  refine ⟨j,i,?_⟩
  have he := Finsupp.sub_add_single_one_cancel hi
  rw [hj] at he
  exact he.symm

theorem positive_jet {a : J I →₀ ℕ} {n d : ℕ}
    (ha : Finsupp.weight weight a = (n,d)) (hd : d ≠ 0) :
    ∃ j, a j ≠ 0 ∧ order j.2 ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hz : Finsupp.weight (fun j : J I => order j.2) a = 0 := by
    rw [Finsupp.weight_apply,Finsupp.sum]
    apply Finset.sum_eq_zero
    intro j hj
    simp [h j (Finsupp.mem_support_iff.mp hj)]
  rw [← weight_snd,ha] at hz
  exact hd hz

theorem residual_weight {a : J I →₀ ℕ} {n d k : ℕ} {j : J I}
    (ha : Finsupp.weight weight a = (n+1,d+k)) (hj : a j ≠ 0) (hk : order j.2 = k) :
    Finsupp.weight weight (a-Finsupp.single j 1) = (n,d) := by
  have hw := Finsupp.weight_sub_single_add (w := weight) hj
  rw [ha] at hw
  apply Prod.ext
  · have h := congrArg Prod.fst hw
    simp only [Prod.fst_add,weight] at h
    omega
  · have h := congrArg Prod.snd hw
    simp only [Prod.snd_add,weight,hk] at h
    omega

def first (i : I) : J I := ((),Finsupp.single i 1)
def second (i j : I) : J I := ((),Finsupp.single i 1+Finsupp.single j 1)

theorem exponent_one {a : J I →₀ ℕ} {n : ℕ}
    (ha : Finsupp.weight weight a = (n+1,1)) :
    ∃ i, a = Finsupp.single ((),0) n+Finsupp.single (first i) 1 := by
  obtain ⟨j,hj,hp⟩ := positive_jet ha (by decide)
  have ho : order j.2 = 1 := by have h := jet_order_bound ha hj; omega
  obtain ⟨i,hi⟩ := order_one ho
  have he : j = first i := Prod.ext (Subsingleton.elim _ _) hi
  have hw := residual_weight (d := 0) (k := 1) ha hj ho
  have hz := ScalarZeroDerivative.exponent_zero hw
  have hh := Finsupp.sub_add_single_one_cancel hj
  rw [hz,he] at hh
  exact ⟨i,hh.symm⟩

theorem exponent_quartic_two {a : J I →₀ ℕ}
    (ha : Finsupp.weight weight a = (4,2)) :
    (∃ i j, a = Finsupp.single ((),0) 3+Finsupp.single (second i j) 1) ∨
    (∃ i j, a = Finsupp.single ((),0) 2+Finsupp.single (first i) 1+Finsupp.single (first j) 1) := by
  obtain ⟨j,hj,hp⟩ := positive_jet ha (by decide)
  have ho := jet_order_bound ha hj
  have hc : order j.2 = 1 ∨ order j.2 = 2 := by omega
  rcases hc with h1 | h2
  · obtain ⟨i,hi⟩ := order_one h1
    have he : j = first i := Prod.ext (Subsingleton.elim _ _) hi
    have hw := residual_weight (n := 3) (d := 1) (k := 1) ha hj h1
    obtain ⟨k,hk⟩ := exponent_one hw
    have hh := Finsupp.sub_add_single_one_cancel hj
    rw [hk,he] at hh
    exact Or.inr ⟨k,i,hh.symm⟩
  · obtain ⟨i,k,hik⟩ := order_two h2
    have he : j = second i k := Prod.ext (Subsingleton.elim _ _) hik
    have hw := residual_weight (n := 3) (d := 0) (k := 2) ha hj h2
    have hz := ScalarZeroDerivative.exponent_zero hw
    have hh := Finsupp.sub_add_single_one_cancel hj
    rw [hz,he] at hh
    exact Or.inl ⟨i,k,hh.symm⟩
end
end Math.ScalarDegreeTwo
