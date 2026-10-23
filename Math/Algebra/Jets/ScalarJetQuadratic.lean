import Math.RepresentationTheory.Jets.ScalarJetIBP
import Mathlib.Tactic

/-! A complete one-scalar, one-direction, two-field/two-derivative IBP example.
The finite relation is derived from the unbounded ordinary jet derivative. -/
namespace Math.ScalarJetQuadratic
set_option autoImplicit false
noncomputable section
open ScalarJetAlgebra MvPolynomial

abbrev JetIndex := Index Unit Unit
abbrev Poly := ScalarJetAlgebra.Algebra Unit Unit
abbrev Source := grade (S := Unit) (I := Unit) 2 2
abbrev Primitive := grade (S := Unit) (I := Unit) 2 1

def jetIndex (k : ℕ) : JetIndex := ((), Finsupp.single () k)

@[simp] theorem jetIndex_order (k : ℕ) : order (jetIndex k).2 = k := by
  simp [jetIndex, order, Finsupp.weight_single]

theorem index_eq (j : JetIndex) : j = jetIndex (order j.2) := by
  rcases j with ⟨⟨⟩, a⟩
  change ((), a) = ((), Finsupp.single () (order a))
  apply congrArg (fun b : Unit →₀ ℕ => ((), b))
  apply Finsupp.ext
  intro i
  cases i
  simp [order, Finsupp.weight_eq_sum]

theorem jetIndex_injective : Function.Injective jetIndex := by
  intro a b h
  simpa using congrArg (fun j : JetIndex => order j.2) h

def firstExponent : JetIndex →₀ ℕ := Finsupp.single (jetIndex 1) 2
def secondExponent : JetIndex →₀ ℕ :=
  Finsupp.single (jetIndex 0) 1 + Finsupp.single (jetIndex 2) 1
def primitiveExponent : JetIndex →₀ ℕ :=
  Finsupp.single (jetIndex 0) 1 + Finsupp.single (jetIndex 1) 1

theorem exponent_expansion {a : JetIndex →₀ ℕ} {d : ℕ}
    (ha : Finsupp.weight weight a = (2, d)) (hd : d ≤ 2) :
    a = Finsupp.single (jetIndex 0) (a (jetIndex 0)) +
      Finsupp.single (jetIndex 1) (a (jetIndex 1)) +
      Finsupp.single (jetIndex 2) (a (jetIndex 2)) := by
  classical
  ext j
  have hj (k : ℕ) : jetIndex k = j ↔ order j.2 = k := by
    constructor
    · rintro rfl; simp
    · intro h; rw [index_eq j, h]
  by_cases h : a j = 0
  · by_cases h0 : jetIndex 0 = j
    · subst j; simp [jetIndex]
    · by_cases h1 : jetIndex 1 = j
      · subst j; simp [jetIndex]
      · by_cases h2 : jetIndex 2 = j
        · subst j; simp [jetIndex]
        · simp [h0, h1, h2, h]
  · have hb := jet_order_bound ha h
    have hc : order j.2 = 0 ∨ order j.2 = 1 ∨ order j.2 = 2 := by omega
    rcases hc with hc | hc | hc
    · have he := (hj 0).mpr hc; subst j; simp [jetIndex]
    · have he := (hj 1).mpr hc; subst j; simp [jetIndex]
    · have he := (hj 2).mpr hc; subst j; simp [jetIndex]

theorem exponent_grade_two {a : JetIndex →₀ ℕ}
    (ha : Finsupp.weight weight a = (2, 2)) : a = firstExponent ∨ a = secondExponent := by
  have he := exponent_expansion ha (by decide)
  have hw := ha
  rw [he] at hw
  simp [map_add, Finsupp.weight_single, weight] at hw
  have hcases :
      (a (jetIndex 0) = 0 ∧ a (jetIndex 1) = 2 ∧ a (jetIndex 2) = 0) ∨
      (a (jetIndex 0) = 1 ∧ a (jetIndex 1) = 0 ∧ a (jetIndex 2) = 1) := by omega
  rcases hcases with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · left; simpa [h0, h1, h2, firstExponent] using he
  · right; simpa [h0, h1, h2, secondExponent] using he

theorem exponent_grade_one {a : JetIndex →₀ ℕ}
    (ha : Finsupp.weight weight a = (2, 1)) : a = primitiveExponent := by
  have he := exponent_expansion ha (by decide)
  have hw := ha
  rw [he] at hw
  simp [map_add, Finsupp.weight_single, weight] at hw
  have h0 : a (jetIndex 0) = 1 := by omega
  have h1 : a (jetIndex 1) = 1 := by omega
  have h2 : a (jetIndex 2) = 0 := by omega
  simpa [h0, h1, h2, primitiveExponent] using he

def first : Source := ⟨monomial firstExponent 1,
  MvPolynomial.isWeightedHomogeneous_monomial weight _ _ (by
    simp [firstExponent, Finsupp.weight_single, weight])⟩

def second : Source := ⟨monomial secondExponent 1,
  MvPolynomial.isWeightedHomogeneous_monomial weight _ _ (by
    simp [secondExponent, map_add, Finsupp.weight_single, weight])⟩

def primitive : Primitive := ⟨monomial primitiveExponent 1,
  MvPolynomial.isWeightedHomogeneous_monomial weight _ _ (by
    simp [primitiveExponent, map_add, Finsupp.weight_single, weight])⟩

theorem exponents_ne : firstExponent ≠ secondExponent := by
  intro h
  have he := congrArg (fun a : JetIndex →₀ ℕ => a (jetIndex 1)) h
  norm_num [firstExponent, secondExponent, jetIndex, Finsupp.single_apply] at he

theorem source_reconstruct (p : Source) :
    p = p.val.coeff firstExponent • first + p.val.coeff secondExponent • second := by
  classical
  apply Subtype.ext
  apply MvPolynomial.ext
  intro a
  by_cases ha : a = firstExponent
  · subst a; simp [first, second, Ne.symm exponents_ne]
  · by_cases hb : a = secondExponent
    · subst a; simp [first, second, exponents_ne]
    · have hz : p.val.coeff a = 0 := by
        by_contra h
        exact (exponent_grade_two (p.property h)).elim ha hb
      simp [first, second, coeff_monomial, Ne.symm ha, Ne.symm hb, hz]

theorem primitive_reconstruct (p : Primitive) :
    p = p.val.coeff primitiveExponent • primitive := by
  apply Subtype.ext
  change p.val = p.val.coeff primitiveExponent • monomial primitiveExponent 1
  rw [smul_monomial, smul_eq_mul, mul_one]
  apply MvPolynomial.IsWeightedHomogeneous.eq_monomial_of_unique_weight p.property
  intro a ha
  exact exponent_grade_one ha

theorem derivative_primitive : derivative () 2 1 primitive = first + second := by
  apply Subtype.ext
  change totalDerivative () (monomial primitiveExponent 1 : Poly) =
    monomial firstExponent 1 + monomial secondExponent 1
  rw [primitiveExponent, MvPolynomial.monomial_add_single]
  simp only [pow_one]
  change totalDerivative () (X (jetIndex 0) * X (jetIndex 1) : Poly) = _
  rw [totalDerivative_mul]
  simp only [totalDerivative_X]
  have hshift (k : ℕ) : shift () (jetIndex k) = jetIndex (k + 1) := by
    simp [shift, jetIndex, ← Finsupp.single_add]
  rw [hshift, hshift]
  simp only [firstExponent, secondExponent, ← X_pow_eq_monomial, monomial_add_single, pow_one]
  ring

theorem source_span : Submodule.span ℂ ({first, second} : Set Source) = ⊤ := by
  apply top_unique
  intro p _
  rw [source_reconstruct p]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem relations_span : ScalarJetIBP.relations Unit Unit 2 1 = ℂ ∙ (first + second) := by
  apply le_antisymm
  · rintro p ⟨c, rfl⟩
    have hc : c = Finsupp.single () (c ()) := by ext i; cases i; simp
    rw [hc, ScalarJetIBP.divergence_single, primitive_reconstruct (c ()),
      map_smul, derivative_primitive]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_singleton_le_iff_mem]
    rw [← derivative_primitive]
    exact ScalarJetIBP.derivative_mem_relations 2 1 () primitive

def reduction : Source →ₗ[ℂ] ℂ :=
  ((MvPolynomial.lcoeff ℂ firstExponent).comp Source.subtype) -
    ((MvPolynomial.lcoeff ℂ secondExponent).comp Source.subtype)

@[simp] theorem reduction_first : reduction first = 1 := by
  simp [reduction, first, exponents_ne]

@[simp] theorem reduction_second : reduction second = -1 := by
  simp [reduction, second, Ne.symm exponents_ne]

theorem reduction_ker : LinearMap.ker reduction = ScalarJetIBP.relations Unit Unit 2 1 := by
  rw [relations_span]
  ext p
  constructor
  · intro hp
    have h : p.val.coeff firstExponent = p.val.coeff secondExponent :=
      sub_eq_zero.mp hp
    rw [Submodule.mem_span_singleton]
    refine ⟨p.val.coeff firstExponent, ?_⟩
    rw [smul_add, h]
    simpa only [h] using (source_reconstruct p).symm
  · intro hp
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hp
    change reduction (c • (first + second)) = 0
    simp

theorem reduction_surjective : Function.Surjective reduction := by
  intro c
  exact ⟨c • first, by simp⟩

abbrev Quotient := Source ⧸ ScalarJetIBP.relations Unit Unit 2 1

def quotientEquiv : Quotient ≃ₗ[ℂ] ℂ :=
  (Submodule.quotEquivOfEq _ _ reduction_ker.symm).trans
    (reduction.quotKerEquivOfSurjective reduction_surjective)

@[simp] theorem quotientEquiv_mk (p : Source) :
    quotientEquiv (Submodule.Quotient.mk p) = reduction p := rfl

theorem quotient_finrank : Module.finrank ℂ Quotient = 1 := by
  rw [quotientEquiv.finrank_eq]
  exact Module.finrank_self ℂ

theorem first_survives : (ScalarJetIBP.relations Unit Unit 2 1).mkQ first ≠ 0 := by
  intro h
  have he : reduction first = 0 := by
    calc
      reduction first = quotientEquiv ((ScalarJetIBP.relations Unit Unit 2 1).mkQ first) := rfl
      _ = quotientEquiv 0 := congrArg quotientEquiv h
      _ = 0 := map_zero quotientEquiv
  exact one_ne_zero (reduction_first.symm.trans he)

theorem ibp_identity : (ScalarJetIBP.relations Unit Unit 2 1).mkQ second =
    -(ScalarJetIBP.relations Unit Unit 2 1).mkQ first := by
  apply quotientEquiv.injective
  simp

end
end Math.ScalarJetQuadratic
