import Math.Algebra.Jets.ScalarJetGrading

/-! The complete single-scalar source at derivative degree zero, at every
field degree. Reconstruction uses the actual weighted monomial support. -/
namespace Math.ScalarZeroDerivative
set_option autoImplicit false
noncomputable section
open ScalarJetAlgebra MvPolynomial
variable {I : Type*}
abbrev J (I : Type*) := ScalarJetAlgebra.Index Unit I
def exponent (n : ℕ) : J I →₀ ℕ := Finsupp.single ((),0) n

theorem exponent_zero {n : ℕ} {a : J I →₀ ℕ}
    (ha : Finsupp.weight weight a = (n,0)) : a = exponent n := by
  classical
  have hs (j : J I) (hj : a j ≠ 0) : j = ((),0) := by
    have ho := jet_order_bound ha hj
    have hz : j.2 = 0 := by
      ext i
      have hi := Finsupp.le_weight (fun _ : I => 1) (s := i) (by decide) j.2
      change j.2 i ≤ order j.2 at hi
      exact Nat.eq_zero_of_le_zero (hi.trans ho)
    exact Prod.ext (Subsingleton.elim _ _) hz
  have he : a = Finsupp.single ((),0) (a ((),0)) := by
    ext j
    by_cases hj : j = ((),0)
    · subst j; simp
    · have hz : a j = 0 := by by_contra hn; exact hj (hs j hn)
      simp [hj,hz]
  have hn : a ((),0) = n := by
    rw [he,Finsupp.weight_single] at ha
    simpa [weight] using congrArg Prod.fst ha
  rw [he,hn]
  rfl

theorem reconstruction (n : ℕ) (p : grade (S := Unit) (I := I) n 0) :
    p.val = monomial (exponent n) (p.val.coeff (exponent n)) := by
  classical
  apply MvPolynomial.ext
  intro a
  by_cases ha : a = exponent n
  · subst a; simp
  · have hz : p.val.coeff a = 0 := by
      by_contra hn
      exact ha (exponent_zero (p.property hn))
    simp [coeff_monomial,ha,eq_comm,hz]

def monomialSource (n : ℕ) (c : ℂ) : grade (S := Unit) (I := I) n 0 :=
  ⟨monomial (exponent n) c,by
    apply MvPolynomial.isWeightedHomogeneous_monomial
    simp [exponent,Finsupp.weight_single,weight,order]⟩

def coordinate (n : ℕ) : grade (S := Unit) (I := I) n 0 →ₗ[ℂ] ℂ :=
  (MvPolynomial.lcoeff ℂ (exponent n)).comp (grade n 0).subtype

def equivalence (n : ℕ) : grade (S := Unit) (I := I) n 0 ≃ₗ[ℂ] ℂ where
  toLinearMap := coordinate n
  invFun := monomialSource n
  left_inv p := Subtype.ext (reconstruction n p).symm
  right_inv c := by
    classical
    change ((monomial (exponent n)) c).coeff (exponent n) = c
    simp only [coeff_monomial,ite_true]

theorem generator_value (n : ℕ) : (monomialSource (I := I) n 1).val =
    (X ((),0) : Algebra Unit I)^n := by
  simp [monomialSource,exponent,X_pow_eq_monomial]

theorem dimension (n : ℕ) : Module.finrank ℂ (grade (S := Unit) (I := I) n 0) = 1 := by
  rw [(equivalence n).finrank_eq]
  exact Module.finrank_self ℂ

end
end Math.ScalarZeroDerivative
