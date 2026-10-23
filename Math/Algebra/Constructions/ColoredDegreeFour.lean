import Math.Algebra.Constructions.ScalarDegreeFour

/-! Four-field source coverage for arbitrary independent field labels. -/
namespace Math.ColoredDegreeFour
set_option autoImplicit false
noncomputable section
open ScalarJetAlgebra MvPolynomial
variable {S I : Type*}
abbrev J (S I : Type*) := Index S I

theorem extract_field {a : J S I →₀ ℕ} {n : ℕ}
    (ha : Finsupp.weight (fun _ : J S I => (1 : ℕ)) a = n+1) :
    ∃ j b, a = b+Finsupp.single j 1 ∧
      Finsupp.weight (fun _ : J S I => (1 : ℕ)) b = n := by
  classical
  have hn : ∃ j, a j ≠ 0 := by
    by_contra h
    push Not at h
    have hz : a = 0 := Finsupp.ext h
    simp [hz] at ha
  obtain ⟨j,hj⟩ := hn
  refine ⟨j,a-Finsupp.single j 1,(Finsupp.sub_add_single_one_cancel hj).symm,?_⟩
  have h := Finsupp.weight_sub_single_add (w := fun _ : J S I => (1 : ℕ)) hj
  rw [ha] at h
  simpa using Nat.add_right_cancel h

theorem fields_zero {a : J S I →₀ ℕ}
    (ha : Finsupp.weight (fun _ : J S I => (1 : ℕ)) a = 0) : a = 0 := by
  ext j
  have h := Finsupp.le_weight (fun _ : J S I => (1 : ℕ)) (s := j) (by decide) a
  simpa [ha] using h

theorem exponent_four {a : J S I →₀ ℕ} {d : ℕ}
    (ha : Finsupp.weight weight a = (4,d)) :
    ∃ j k l m, a = Finsupp.single j 1+Finsupp.single k 1+
      Finsupp.single l 1+Finsupp.single m 1 ∧
      order j.2+order k.2+order l.2+order m.2 = d := by
  have hn : Finsupp.weight (fun _ : J S I => (1 : ℕ)) a = 4 := by
    rw [← weight_fst,ha]
  obtain ⟨m,b,hm,hb⟩ := extract_field hn
  obtain ⟨l,c,hl,hc⟩ := extract_field hb
  obtain ⟨k,e,hk,he⟩ := extract_field hc
  obtain ⟨j,z,hj,hz⟩ := extract_field he
  have h0 := fields_zero hz
  have hex : a = Finsupp.single j 1+Finsupp.single k 1+
      Finsupp.single l 1+Finsupp.single m 1 := by
    rw [hm,hl,hk,hj,h0,zero_add]
  refine ⟨j,k,l,m,hex,?_⟩
  have hd := congrArg Prod.snd ha
  rw [hex] at hd
  simpa [weight,Finsupp.weight_single] using hd

theorem monomial_four {a : J S I →₀ ℕ} {d : ℕ}
    (ha : Finsupp.weight weight a = (4,d)) :
    ∃ j k l m, (monomial a (1 : ℂ) : Algebra S I) = X j*X k*X l*X m ∧
      order j.2+order k.2+order l.2+order m.2 = d := by
  obtain ⟨j,k,l,m,he,hd⟩ := exponent_four ha
  refine ⟨j,k,l,m,?_,hd⟩
  simp [he,monomial_add_single,← X_pow_eq_monomial]

end
end Math.ColoredDegreeFour
