import Math.RepresentationTheory.Coefficients.InputPresentation
import Math.RepresentationTheory.Jets.JetConstantProjection
import Math.Algebra.Constructions.ScalarZeroDerivative

/-! Actual two-species, one-direction free EOM/IBP controls.
Zero-derivative sectors are complete. Positive-degree identities alone
do not assert completeness of a selected finite list. -/
namespace Math.TwoSpeciesDerivativeChecks
set_option autoImplicit false
noncomputable section
open MvPolynomial ScalarJetAlgebra

abbrev A := ScalarJetAlgebra.Algebra (Fin 2) Unit
abbrev D := ScalarJetAlgebra.totalDerivative (S := Fin 2) (I := Unit)
def field (s : Fin 2) : A := X (s,0)
def first (s : Fin 2) : A := D () (field s)
def seed (s : Fin 2) : A := D () (first s)
def equations : Set A := Set.range seed
abbrev T := DifferentialEquation.combined D equations
def input : DerivativeInterface.Input Unit A where
  action := Representation.trivial ℂ Unit A
  relations := T
  stable _ := le_refl _
abbrev q := input.projection

def speciesWeight (j : Index (Fin 2) Unit) : ℕ := if j.1 = 0 then 1 else 0
def exponent (r s : ℕ) : Index (Fin 2) Unit →₀ ℕ :=
  Finsupp.single (0,0) r+Finsupp.single (1,0) s
def V (r s : ℕ) : Submodule ℂ A := grade (r+s) 0 ⊓
  MvPolynomial.weightedHomogeneousSubmodule ℂ speciesWeight r

theorem exponent_complete {r s : ℕ} {a : Index (Fin 2) Unit →₀ ℕ}
    (ha : Finsupp.weight weight a = (r+s,0))
    (hr : Finsupp.weight speciesWeight a = r) : a = exponent r s := by
  classical
  have hz {j : Index (Fin 2) Unit} (hj : a j ≠ 0) : j.2 = 0 := by
    have h := jet_order_bound ha hj
    apply Finsupp.ext
    intro i
    change j.2 i = 0
    have hi := Finsupp.le_weight (fun _ : Unit => 1) (s := i) (by decide) j.2
    change j.2 i ≤ order j.2 at hi
    exact Nat.eq_zero_of_le_zero (hi.trans h)
  have he : a = Finsupp.single (0,0) (a (0,0))+
      Finsupp.single (1,0) (a (1,0)) := by
    ext j
    by_cases hj : j.2 = 0
    · rcases j with ⟨j,k⟩
      change k = 0 at hj
      subst k
      fin_cases j <;> simp
    · have h0 : a j = 0 := by by_contra hn; exact hj (hz hn)
      have h1 : (0,0) ≠ j := by intro h; exact hj (congrArg Prod.snd h.symm)
      have h2 : (1,0) ≠ j := by intro h; exact hj (congrArg Prod.snd h.symm)
      simp [h0,h1,h2]
  have h := hr
  rw [he] at h
  simp [speciesWeight,Finsupp.weight_single] at h
  have hn := congrArg Prod.fst ha
  rw [he] at hn
  simp [weight,Finsupp.weight_single] at hn
  have hs : a (1,0) = s := by omega
  rw [he,h,hs]
  rfl

theorem source_reconstruction (r s : ℕ) (p : V r s) :
    p.val = monomial (exponent r s) (p.val.coeff (exponent r s)) := by
  classical
  apply MvPolynomial.ext
  intro a
  by_cases ha : a = exponent r s
  · subst a; simp
  · have hz : p.val.coeff a = 0 := by
      by_contra hn
      exact ha (exponent_complete (p.property.1 hn) (p.property.2 hn))
    simp [coeff_monomial,ha,eq_comm,hz]

def generator (r s : ℕ) : V r s := ⟨monomial (exponent r s) 1,by
  constructor
  · apply MvPolynomial.isWeightedHomogeneous_monomial
    simp [exponent,weight,order,Finsupp.weight_single]
  · apply MvPolynomial.isWeightedHomogeneous_monomial
    simp [exponent,speciesWeight,Finsupp.weight_single]⟩

def evaluation : A →ₐ[ℂ] MvPolynomial (Fin 2) ℂ := JetConstantProjection.constantJets
def functional (r s : ℕ) : A →ₗ[ℂ] ℂ :=
  (MvPolynomial.lcoeff ℂ (Finsupp.single 0 r+Finsupp.single 1 s)).comp evaluation.toLinearMap

theorem evaluation_equations {p : A} (hp : p ∈ DifferentialEquation.ideal D equations) :
    evaluation p = 0 := by
  have hle : DifferentialEquation.ideal D equations ≤
      (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)).comap evaluation.toRingHom := by
    apply DifferentialEquation.minimal
    · rintro _ ⟨s,rfl⟩
      exact JetConstantProjection.constantJets_derivative () (first s)
    · intro i p _
      exact JetConstantProjection.constantJets_derivative i p
  exact hle hp

theorem annihilates (r s : ℕ) : T ≤ (functional r s).ker := by
  apply sup_le
  · intro p hp
    change (evaluation p).coeff _ = 0
    rw [evaluation_equations hp]
    simp
  · rintro _ ⟨v,rfl⟩
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simpa only [map_add] using (functional r s).ker.add_mem hv hw
    | single i p =>
      rw [DifferentialEquation.divergence_single]
      change (JetConstantProjection.constantJets (D i p)).coeff _ = 0
      rw [JetConstantProjection.constantJets_derivative]
      simp

theorem detects (r s : ℕ) : functional r s (generator r s).val = 1 := by
  have he : (generator r s).val = field 0^r*field 1^s := by
    simp [generator,field,exponent,X_pow_eq_monomial,monomial_mul_monomial]
  rw [he]
  change (evaluation (field 0^r*field 1^s)).coeff _ = 1
  rw [map_mul,map_pow,map_pow]
  have h0 : evaluation (field 0) = X 0 := by simp [evaluation,field,JetConstantProjection.constantJets_X]
  have h1 : evaluation (field 1) = X 1 := by simp [evaluation,field,JetConstantProjection.constantJets_X]
  rw [h0,h1]
  simp [X_pow_eq_monomial,monomial_mul_monomial]

abbrev Image (r s : ℕ) := input.selectedImage (V r s)
def imageGenerator (r s : ℕ) : Image r s := ⟨q (generator r s).val,⟨generator r s,rfl⟩⟩
def imageCoordinate (r s : ℕ) : Image r s →ₗ[ℂ] ℂ :=
  (T.liftQ (functional r s) (annihilates r s)).comp (input.selectedImage (V r s)).subtype

theorem image_reconstruction (r s : ℕ) (x : Image r s) :
    x = imageCoordinate r s x • imageGenerator r s := by
  obtain ⟨p,hp⟩ := x.property
  have he : p.val = p.val.coeff (exponent r s) • (generator r s).val := by
    rw [source_reconstruction r s p]
    simp [generator,MvPolynomial.smul_monomial]
  have hx : x = p.val.coeff (exponent r s) • imageGenerator r s := by
    apply Subtype.ext
    rw [← hp]
    change q p.val = _
    calc
      q p.val = q (p.val.coeff (exponent r s) • (generator r s).val) := congrArg q he
      _ = p.val.coeff (exponent r s) • q (generator r s).val := map_smul q _ _
  have hc := congrArg (imageCoordinate r s) hx
  rw [map_smul] at hc
  change imageCoordinate r s x = _ • functional r s (generator r s).val at hc
  rw [detects,smul_eq_mul,mul_one] at hc
  exact hx.trans (congrArg (fun c : ℂ => c • imageGenerator r s) hc.symm)

def imageEquiv (r s : ℕ) : Image r s ≃ₗ[ℂ] ℂ where
  toLinearMap := imageCoordinate r s
  invFun c := c • imageGenerator r s
  left_inv x := (image_reconstruction r s x).symm
  right_inv c := by
    change imageCoordinate r s (c • imageGenerator r s) = c
    rw [map_smul]
    change c • functional r s (generator r s).val = c
    rw [detects,smul_eq_mul,mul_one]

theorem zero_derivative_dimension (r s : ℕ) : Module.finrank ℂ (Image r s) = 1 := by
  rw [(imageEquiv r s).finrank_eq]
  exact Module.finrank_self ℂ

theorem seed_zero (s : Fin 2) : q (seed s) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr
    (Submodule.mem_sup_left (DifferentialEquation.seed_mem D equations ⟨s,rfl⟩))

theorem first_product_zero : q (first 0*first 1) = 0 := by
  have he : field 0*seed 1 ∈ DifferentialEquation.ideal D equations :=
    (DifferentialEquation.ideal D equations).mul_mem_left _
      (DifferentialEquation.seed_mem D equations ⟨1,rfl⟩)
  have hd := DifferentialEquation.derivative_mem_ibp D () (field 0*first 1)
  have h : first 0*first 1 ∈ T := by
    have hs := T.sub_mem (Submodule.mem_sup_right hd) (Submodule.mem_sup_left he)
    convert hs using 1
    rw [ScalarJetAlgebra.totalDerivative_mul]
    dsimp [first,seed]
    ring
  exact (Submodule.Quotient.mk_eq_zero _).mpr h

theorem integration_by_parts : q (first 0*field 1) = -q (field 0*first 1) := by
  have h := (Submodule.Quotient.mk_eq_zero T).mpr
    (Submodule.mem_sup_right (DifferentialEquation.derivative_mem_ibp D () (field 0*field 1)))
  change q (D () (field 0*field 1)) = 0 at h
  rw [ScalarJetAlgebra.totalDerivative_mul,map_add] at h
  change q (first 0*field 1) = -q (field 0*first 1)
  rw [mul_comm (field 1)] at h
  apply eq_neg_of_add_eq_zero_left
  simpa only [add_comm,first] using h

theorem rescaled_equations (c : ℂ) (hc : c ≠ 0) :
    TwoSidedDifferential.combined (fun i => (D i).toLinearMap)
      ((fun p : A => c • p) '' equations) = T := by
  rw [InputPresentation.scaled_combined _ _ c hc,TwoSidedDifferential.commutative_combined]

theorem recombined_equations (c : ℂ) :
    TwoSidedDifferential.combined (fun i => (D i).toLinearMap)
      (Set.range (Function.update seed 1 (seed 1+c • seed 0))) = T := by
  rw [InputPresentation.recombined_combined _ seed (by decide : (0 : Fin 2) ≠ 1) c,
    TwoSidedDifferential.commutative_combined]
  rfl

def coefficient (r s : ℕ) : input.Coefficient := ⟨{
  toLinearMap := functional r s
  isIntertwining' _ := rfl },fun _ hp => annihilates r s hp⟩

def swapSpecies : A ≃ₗ[ℂ] A :=
  (MvPolynomial.renameEquiv ℂ
    (Equiv.prodCongr (Equiv.swap (0 : Fin 2) 1) (Equiv.refl (Unit →₀ ℕ)))).toLinearEquiv

theorem swapped_value (r s : ℕ) :
    (InputPresentation.reexpressCoefficients input swapSpecies (coefficient r s)).val
      (swapSpecies (generator r s).val) = 1 :=
  (InputPresentation.reexpress_evaluation input swapSpecies (coefficient r s) _).trans (detects r s)

/-- Includes non-diagonal changes; the new action and relations are explicit. -/
theorem basis_change_value (b : A ≃ₗ[ℂ] A) (r s : ℕ) :
    (InputPresentation.reexpress input b).coefficientEquiv
      (InputPresentation.reexpressCoefficients input b (coefficient r s))
      ((InputPresentation.reexpress input b).projection (b (generator r s).val)) = 1 :=
  (InputPresentation.reexpress_evaluation input b (coefficient r s) _).trans (detects r s)

theorem second_product_zero (s t : Fin 2) : q (seed s*field t) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_sup_left
    ((DifferentialEquation.ideal D equations).mul_mem_right _
      (DifferentialEquation.seed_mem D equations ⟨s,rfl⟩)))

def twoDerivativeCandidates : Submodule ℂ A :=
  Submodule.span ℂ ({first 0*first 1,seed 0*field 1,field 0*seed 1} : Set A)

theorem twoDerivativeCandidates_zero {p : A} (hp : p ∈ twoDerivativeCandidates) : q p = 0 := by
  have hle : twoDerivativeCandidates ≤ q.ker := by
    apply Submodule.span_le.mpr
    intro p hp
    rcases hp with hp | hp | hp
    · subst p; exact first_product_zero
    · subst p; exact second_product_zero 0 1
    · rw [Set.mem_singleton_iff] at hp
      subst p
      rw [mul_comm]
      exact second_product_zero 1 0
  exact hle hp

namespace Bilinear
abbrev J := Index (Fin 2) Unit
def index (s : Fin 2) (k : ℕ) : J := (s,Finsupp.single () k)
def e (a b : ℕ) : J →₀ ℕ := Finsupp.single (index 0 a) 1+Finsupp.single (index 1 b) 1
abbrev Source := grade (S := Fin 2) (I := Unit) 2 2 ⊓
  MvPolynomial.weightedHomogeneousSubmodule ℂ speciesWeight 1

theorem order_index (s : Fin 2) (k : ℕ) : order (index s k).2 = k := by
  simp [index,order,Finsupp.weight_single]

theorem index_eq (j : J) : j = index j.1 (order j.2) := by
  apply Prod.ext
  · rfl
  apply Finsupp.ext
  intro i
  cases i
  simp [index,order,Finsupp.weight_eq_sum]

theorem expansion {a : J →₀ ℕ} (ha : Finsupp.weight weight a = (2,2)) :
    a = Finsupp.single (index 0 0) (a (index 0 0))+
      Finsupp.single (index 0 1) (a (index 0 1))+
      Finsupp.single (index 0 2) (a (index 0 2))+
      Finsupp.single (index 1 0) (a (index 1 0))+
      Finsupp.single (index 1 1) (a (index 1 1))+
      Finsupp.single (index 1 2) (a (index 1 2)) := by
  ext j
  by_cases hj : a j = 0
  · by_cases h0 : j = index 0 0
    · subst j; simp [index]
    · by_cases h1 : j = index 0 1
      · subst j; simp [index]
      · by_cases h2 : j = index 0 2
        · subst j; simp [index]
        · by_cases h3 : j = index 1 0
          · subst j; simp [index]
          · by_cases h4 : j = index 1 1
            · subst j; simp [index]
            · by_cases h5 : j = index 1 2
              · subst j; simp [index]
              · simp [hj,Ne.symm h0,Ne.symm h1,Ne.symm h2,Ne.symm h3,Ne.symm h4,Ne.symm h5]
  · have hb := jet_order_bound ha hj
    have hk : order j.2 = 0 ∨ order j.2 = 1 ∨ order j.2 = 2 := by omega
    rcases j with ⟨js,jk⟩
    have he := index_eq (js,jk)
    change (js,jk) = index js (order jk) at he
    change order jk = 0 ∨ order jk = 1 ∨ order jk = 2 at hk
    rcases hk with hk | hk | hk <;> rw [he,hk] <;>
      fin_cases js <;> simp [index]

theorem speciesWeight_index (s : Fin 2) (k : ℕ) :
    speciesWeight (index s k) = if s = 0 then 1 else 0 := rfl

theorem classify {a : J →₀ ℕ} (ha : Finsupp.weight weight a = (2,2))
    (hr : Finsupp.weight speciesWeight a = 1) : a = e 1 1 ∨ a = e 2 0 ∨ a = e 0 2 := by
  have he := expansion ha
  have hw := ha
  have hs := hr
  rw [he] at hw hs
  simp [Finsupp.weight_single,weight,order_index] at hw
  simp [Finsupp.weight_single,speciesWeight_index] at hs
  change a (index 0 0)+a (index 0 1)+a (index 0 2) = 1 at hs
  have hc :
    (a (index 0 0) = 0 ∧ a (index 0 1) = 1 ∧ a (index 0 2) = 0 ∧
      a (index 1 0) = 0 ∧ a (index 1 1) = 1 ∧ a (index 1 2) = 0) ∨
    (a (index 0 0) = 0 ∧ a (index 0 1) = 0 ∧ a (index 0 2) = 1 ∧
      a (index 1 0) = 1 ∧ a (index 1 1) = 0 ∧ a (index 1 2) = 0) ∨
    (a (index 0 0) = 1 ∧ a (index 0 1) = 0 ∧ a (index 0 2) = 0 ∧
      a (index 1 0) = 0 ∧ a (index 1 1) = 0 ∧ a (index 1 2) = 1) := by omega
  rcases hc with ⟨h0,h1,h2,h3,h4,h5⟩ | ⟨h0,h1,h2,h3,h4,h5⟩ | ⟨h0,h1,h2,h3,h4,h5⟩
  · exact Or.inl (by simpa [h0,h1,h2,h3,h4,h5,e] using he)
  · exact Or.inr (Or.inl (by simpa [h0,h1,h2,h3,h4,h5,e,add_comm] using he))
  · exact Or.inr (Or.inr (by simpa [h0,h1,h2,h3,h4,h5,e] using he))

theorem monomial_zero {a : J →₀ ℕ} (ha : Finsupp.weight weight a = (2,2))
    (hr : Finsupp.weight speciesWeight a = 1) (c : ℂ) : q (monomial a c) = 0 := by
  have he0 : (monomial (e 1 1) 1 : A) = first 0*first 1 := by
    simp [e,first,field,index,shift,monomial_add_single,← X_pow_eq_monomial]
  have he1 : (monomial (e 2 0) 1 : A) = seed 0*field 1 := by
    simp [e,seed,first,field,index,shift,← Finsupp.single_add,
      monomial_add_single,← X_pow_eq_monomial]
  have he2 : (monomial (e 0 2) 1 : A) = field 0*seed 1 := by
    simp [e,seed,first,field,index,shift,← Finsupp.single_add,
      monomial_add_single,← X_pow_eq_monomial]
  have h : q (monomial a 1) = 0 := by
    rcases classify ha hr with h | h | h
    · rw [h,he0]; exact first_product_zero
    · rw [h,he1]; exact second_product_zero 0 1
    · rw [h,he2,mul_comm]; exact second_product_zero 1 0
  have hm : (monomial a c : A) = c • monomial a 1 := by simp [smul_monomial]
  rw [hm,map_smul,h,smul_zero]

theorem full_source_zero (p : Source) : q p.val = 0 := by
  rw [p.val.as_sum,map_sum]
  apply Finset.sum_eq_zero
  intro a ha
  have hn := MvPolynomial.mem_support_iff.mp ha
  exact monomial_zero (p.property.1 hn) (p.property.2 hn) _

theorem image_dimension : Module.finrank ℂ (input.selectedImage Source) = 0 := by
  have hz (x : input.selectedImage Source) : x = 0 := by
    apply Subtype.ext
    obtain ⟨p,hp⟩ := x.property
    exact hp.symm.trans (full_source_zero p)
  have : Subsingleton (input.selectedImage Source) := ⟨fun a b => (hz a).trans (hz b).symm⟩
  exact Module.finrank_zero_of_subsingleton
end Bilinear

end
end Math.TwoSpeciesDerivativeChecks
