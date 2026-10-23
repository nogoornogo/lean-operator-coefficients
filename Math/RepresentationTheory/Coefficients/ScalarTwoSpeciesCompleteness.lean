import Math.Algebra.Jets.ScalarFirstJetReduction

/-! Complete actual finite C1 positive-derivative sources. -/
namespace Math.ScalarTwoSpeciesCompleteness
set_option autoImplicit false
noncomputable section
open MvPolynomial ScalarJetAlgebra TwoSpeciesDerivativeChecks
open TwoSpeciesDerivativeChecks.Bilinear (index order_index index_eq speciesWeight_index)

abbrev J := Index (Fin 2) Unit
def source (r d : ℕ) : Submodule ℂ A := grade (2*(r+1)) d ⊓
  weightedHomogeneousSubmodule ℂ speciesWeight (r+1)

theorem expansion {a : J →₀ ℕ} {n d : ℕ}
    (ha : Finsupp.weight weight a = (n,d)) (hd : d ≤ 2) :
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

def firstA (r : ℕ) : J →₀ ℕ := Finsupp.single (index 0 0) r+
  Finsupp.single (index 0 1) 1+Finsupp.single (index 1 0) (r+1)
def firstB (r : ℕ) : J →₀ ℕ := Finsupp.single (index 0 0) (r+1)+
  Finsupp.single (index 1 0) r+Finsupp.single (index 1 1) 1

theorem first_classify (r : ℕ) {a : J →₀ ℕ}
    (ha : Finsupp.weight weight a = (2*(r+1),1))
    (hr : Finsupp.weight speciesWeight a = r+1) : a = firstA r ∨ a = firstB r := by
  have he := expansion ha (by decide)
  have hw := ha
  have hs := hr
  rw [he] at hw hs
  simp [Finsupp.weight_single,weight,order_index] at hw
  simp [Finsupp.weight_single,speciesWeight_index] at hs
  have hc :
    (a (index 0 0) = r ∧ a (index 0 1) = 1 ∧ a (index 0 2) = 0 ∧
      a (index 1 0) = r+1 ∧ a (index 1 1) = 0 ∧ a (index 1 2) = 0) ∨
    (a (index 0 0) = r+1 ∧ a (index 0 1) = 0 ∧ a (index 0 2) = 0 ∧
      a (index 1 0) = r ∧ a (index 1 1) = 1 ∧ a (index 1 2) = 0) := by omega
  rcases hc with ⟨h0,h1,h2,h3,h4,h5⟩ | ⟨h0,h1,h2,h3,h4,h5⟩
  · left; simpa [firstA,h0,h1,h2,h3,h4,h5] using he
  · right; simpa [firstB,h0,h1,h2,h3,h4,h5] using he

namespace Second

def a : J →₀ ℕ := Finsupp.single (index 0 0) 1+Finsupp.single (index 0 2) 1+
  Finsupp.single (index 1 0) 2
def b : J →₀ ℕ := Finsupp.single (index 0 1) 2+Finsupp.single (index 1 0) 2
def c : J →₀ ℕ := Finsupp.single (index 0 0) 1+Finsupp.single (index 0 1) 1+
  Finsupp.single (index 1 0) 1+Finsupp.single (index 1 1) 1
def d : J →₀ ℕ := Finsupp.single (index 0 0) 2+Finsupp.single (index 1 1) 2
def e : J →₀ ℕ := Finsupp.single (index 0 0) 2+Finsupp.single (index 1 0) 1+
  Finsupp.single (index 1 2) 1

theorem classify {v : J →₀ ℕ} (ha : Finsupp.weight weight v = (4,2))
    (hr : Finsupp.weight speciesWeight v = 2) : v = a ∨ v = b ∨ v = c ∨ v = d ∨ v = e := by
  have he := expansion ha (by decide)
  have hw := ha
  have hs := hr
  rw [he] at hw hs
  simp [Finsupp.weight_single,weight,order_index] at hw
  simp [Finsupp.weight_single,speciesWeight_index] at hs
  by_cases ha2 : v (index 0 2) = 1
  · have hc : v (index 0 0) = 1 ∧ v (index 0 1) = 0 ∧ v (index 0 2) = 1 ∧ v (index 1 0) = 2 ∧ v (index 1 1) = 0 ∧ v (index 1 2) = 0 := by omega
    rcases hc with ⟨h0,h1,h2,h3,h4,h5⟩
    exact Or.inl (by simpa [a,h0,h1,h2,h3,h4,h5] using he)
  by_cases hb2 : v (index 1 2) = 1
  · have hc : v (index 0 0) = 2 ∧ v (index 0 1) = 0 ∧ v (index 0 2) = 0 ∧ v (index 1 0) = 1 ∧ v (index 1 1) = 0 ∧ v (index 1 2) = 1 := by omega
    rcases hc with ⟨h0,h1,h2,h3,h4,h5⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr ((by simpa [e,h0,h1,h2,h3,h4,h5] using he)))))
  by_cases ha1 : v (index 0 1) = 2
  · have hc : v (index 0 0) = 0 ∧ v (index 0 1) = 2 ∧ v (index 0 2) = 0 ∧ v (index 1 0) = 2 ∧ v (index 1 1) = 0 ∧ v (index 1 2) = 0 := by omega
    rcases hc with ⟨h0,h1,h2,h3,h4,h5⟩
    exact Or.inr (Or.inl (by simpa [b,h0,h1,h2,h3,h4,h5] using he))
  by_cases hb1 : v (index 1 1) = 2
  · have hc : v (index 0 0) = 2 ∧ v (index 0 1) = 0 ∧ v (index 0 2) = 0 ∧ v (index 1 0) = 0 ∧ v (index 1 1) = 2 ∧ v (index 1 2) = 0 := by omega
    rcases hc with ⟨h0,h1,h2,h3,h4,h5⟩
    exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa [d,h0,h1,h2,h3,h4,h5] using he))))
  have hc : v (index 0 0) = 1 ∧ v (index 0 1) = 1 ∧ v (index 0 2) = 0 ∧ v (index 1 0) = 1 ∧ v (index 1 1) = 1 ∧ v (index 1 2) = 0 := by omega
  rcases hc with ⟨h0,h1,h2,h3,h4,h5⟩
  exact Or.inr (Or.inr (Or.inl (by simpa [c,h0,h1,h2,h3,h4,h5] using he)))
end Second

def firstWord (r : ℕ) : A := first 0*field 0^r*field 1^(r+1)
def otherWord (r : ℕ) : A := field 0^(r+1)*first 1*field 1^r

def secondWord : A := first 0*field 0*first 1*field 1

theorem firstWord_monomial (r : ℕ) : firstWord r = monomial (firstA r) 1 := by
  rw [firstA,monomial_add_single,monomial_add_single,← X_pow_eq_monomial]
  simp [firstWord,first,field,index,shift]
  ring

theorem otherWord_monomial (r : ℕ) : otherWord r = monomial (firstB r) 1 := by
  rw [firstB,monomial_add_single,monomial_add_single,← X_pow_eq_monomial]
  simp [otherWord,first,field,index,shift]
  ring

theorem secondWord_monomial : secondWord = monomial Second.c 1 := by
  rw [Second.c,monomial_add_single,monomial_add_single,monomial_add_single,← X_pow_eq_monomial]
  simp [secondWord,first,field,index,shift]
  ring

abbrev firstFunctional (r : ℕ) := ScalarFirstJetReduction.onJets (ScalarFirstJetReduction.firstFunctional r)
abbrev secondFunctional := ScalarFirstJetReduction.onJets ScalarFirstJetReduction.secondFunctional

theorem first_annihilates (r : ℕ) : T ≤ (firstFunctional r).ker :=
  ScalarFirstJetReduction.annihilates _ (ScalarFirstJetReduction.first_derivative r)
theorem second_annihilates : T ≤ secondFunctional.ker :=
  ScalarFirstJetReduction.annihilates _ ScalarFirstJetReduction.second_derivative

theorem first_value (r : ℕ) : firstFunctional r (firstWord r) = 1 := by
  have hp : ScalarFirstJetReduction.projection (firstWord r) =
      monomial (ScalarFirstJetReduction.exponent r 1 (r+1) 0) 1 := by
    simp only [firstWord,map_mul,map_pow,ScalarFirstJetReduction.projection_first,
      ScalarFirstJetReduction.projection_field]
    simp only [ScalarFirstJetReduction.exponent,Finsupp.single_zero,add_zero]
    rw [monomial_add_single,monomial_add_single,← X_pow_eq_monomial]
    simp only [pow_one]
    ring
  have hn : ScalarFirstJetReduction.exponent (r+1) 0 r 1 ≠
      ScalarFirstJetReduction.exponent r 1 (r+1) 0 := by
    intro h
    have he := congrArg (fun x => x (0,1)) h
    simp [ScalarFirstJetReduction.exponent] at he
  change ScalarFirstJetReduction.firstFunctional r
    (ScalarFirstJetReduction.projection (firstWord r)) = 1
  rw [hp]
  simp [ScalarFirstJetReduction.firstFunctional,ScalarFirstJetReduction.coefficient,coeff_monomial,Ne.symm hn]

theorem other_value (r : ℕ) : firstFunctional r (otherWord r) = -1 := by
  have hp : ScalarFirstJetReduction.projection (otherWord r) =
      monomial (ScalarFirstJetReduction.exponent (r+1) 0 r 1) 1 := by
    simp only [otherWord,map_mul,map_pow,ScalarFirstJetReduction.projection_first,
      ScalarFirstJetReduction.projection_field]
    simp only [ScalarFirstJetReduction.exponent,Finsupp.single_zero,add_zero]
    rw [monomial_add_single,monomial_add_single,← X_pow_eq_monomial]
    simp only [pow_one]
    ring
  have hn : ScalarFirstJetReduction.exponent r 1 (r+1) 0 ≠
      ScalarFirstJetReduction.exponent (r+1) 0 r 1 := by
    intro h
    have he := congrArg (fun x => x (0,1)) h
    simp [ScalarFirstJetReduction.exponent] at he
  change ScalarFirstJetReduction.firstFunctional r
    (ScalarFirstJetReduction.projection (otherWord r)) = -1
  rw [hp]
  simp [ScalarFirstJetReduction.firstFunctional,ScalarFirstJetReduction.coefficient,coeff_monomial,Ne.symm hn]

theorem derivative_zero (p : A) : q (D () p) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_sup_right
    (DifferentialEquation.derivative_mem_ibp D () p))

theorem first_relation (r : Fin 2) : q (otherWord r.val) = -q (firstWord r.val) := by
  fin_cases r
  · have h := congrArg Neg.neg TwoSpeciesDerivativeChecks.integration_by_parts
    simpa [firstWord,otherWord] using h.symm
  · have hd := derivative_zero (field 0^2*field 1^2)
    have he : D () (field 0^2*field 1^2) =
        (2 : ℂ) • (firstWord 1+otherWord 1) := by
      simp [firstWord,otherWord,pow_two,first,MvPolynomial.smul_eq_C_mul]
      norm_num only [map_ofNat]
      ring
    rw [he,map_smul,map_add] at hd
    have hz := (smul_eq_zero.mp hd).resolve_left (by norm_num : (2 : ℂ) ≠ 0)
    exact eq_neg_of_add_eq_zero_right hz

theorem first_monomial_reconstruction (r : Fin 2) {v : J →₀ ℕ}
    (ha : Finsupp.weight weight v = (2*(r.val+1),1))
    (hr : Finsupp.weight speciesWeight v = r.val+1) (c : ℂ) :
    q (monomial v c) = firstFunctional r.val (monomial v c) • q (firstWord r.val) := by
  have hm : (monomial v c : A) = c • monomial v 1 := by simp [smul_monomial]
  rw [hm,map_smul,map_smul]
  simp only [smul_eq_mul]
  rcases first_classify r.val ha hr with h | h
  · rw [h,← firstWord_monomial,first_value]
    simp
  · rw [h,← otherWord_monomial,other_value,first_relation]
    simp

theorem from_monomials (V : Submodule ℂ A) (f : A →ₗ[ℂ] ℂ) (g : A)
    (h : ∀ p : V, ∀ v ∈ p.val.support,
      q (monomial v (p.val.coeff v)) = f (monomial v (p.val.coeff v)) • q g)
    (p : V) : q p.val = f p.val • q g := by
  have hq := congrArg q p.val.as_sum
  have hf := congrArg f p.val.as_sum
  simp only [map_sum] at hq hf
  rw [hq,hf,Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro v hv
  exact h p v hv

theorem first_reconstruction (r : Fin 2) (p : source r.val 1) :
    q p.val = firstFunctional r.val p.val • q (firstWord r.val) := by
  apply from_monomials (source r.val 1) (firstFunctional r.val) (firstWord r.val) _ p
  intro p v hv
  have hn := MvPolynomial.mem_support_iff.mp hv
  exact first_monomial_reconstruction r (p.property.1 hn) (p.property.2 hn) _


theorem second_value : secondFunctional secondWord = 1 := by
  change ScalarFirstJetReduction.secondFunctional
    (ScalarFirstJetReduction.projection secondWord) = 1
  have hp : ScalarFirstJetReduction.projection secondWord =
      monomial (ScalarFirstJetReduction.exponent 1 1 1 1) 1 := by
    simp only [secondWord,map_mul,ScalarFirstJetReduction.projection_first,
      ScalarFirstJetReduction.projection_field]
    simp [ScalarFirstJetReduction.exponent,monomial_add_single,← X_pow_eq_monomial]
    ring
  rw [hp]
  norm_num [ScalarFirstJetReduction.secondFunctional,ScalarFirstJetReduction.coefficient,
    coeff_monomial,ScalarFirstJetReduction.exponent_eq]

def secondB : A := first 0^2*field 1^2
def secondD : A := field 0^2*first 1^2

theorem secondB_monomial : secondB = monomial Second.b 1 := by
  rw [Second.b,monomial_add_single,← X_pow_eq_monomial]
  simp [secondB,first,field,index,shift]
theorem secondD_monomial : secondD = monomial Second.d 1 := by
  rw [Second.d,monomial_add_single,← X_pow_eq_monomial]
  simp [secondD,first,field,index,shift]

theorem secondB_value : secondFunctional secondB = -2 := by
  change ScalarFirstJetReduction.secondFunctional (ScalarFirstJetReduction.projection secondB) = -2
  have hp : ScalarFirstJetReduction.projection secondB =
      monomial (ScalarFirstJetReduction.exponent 0 2 2 0) 1 := by
    simp only [secondB,map_mul,map_pow,ScalarFirstJetReduction.projection_first,
      ScalarFirstJetReduction.projection_field]
    simp [ScalarFirstJetReduction.exponent,monomial_add_single,← X_pow_eq_monomial]
  rw [hp]
  norm_num [ScalarFirstJetReduction.secondFunctional,ScalarFirstJetReduction.coefficient,
    coeff_monomial,ScalarFirstJetReduction.exponent_eq]

theorem secondD_value : secondFunctional secondD = -2 := by
  change ScalarFirstJetReduction.secondFunctional (ScalarFirstJetReduction.projection secondD) = -2
  have hp : ScalarFirstJetReduction.projection secondD =
      monomial (ScalarFirstJetReduction.exponent 2 0 0 2) 1 := by
    simp only [secondD,map_mul,map_pow,ScalarFirstJetReduction.projection_first,
      ScalarFirstJetReduction.projection_field]
    simp [ScalarFirstJetReduction.exponent,monomial_add_single,← X_pow_eq_monomial]
  rw [hp]
  norm_num [ScalarFirstJetReduction.secondFunctional,ScalarFirstJetReduction.coefficient,
    coeff_monomial,ScalarFirstJetReduction.exponent_eq]

theorem equation_multiple (s : Fin 2) (p : A) : q (p*seed s) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_sup_left
    ((DifferentialEquation.ideal D equations).mul_mem_left _
      (DifferentialEquation.seed_mem D equations ⟨s,rfl⟩)))

theorem secondB_relation : q secondB = (-2 : ℂ) • q secondWord := by
  have hd := derivative_zero (first 0*field 0*field 1^2)
  have he : D () (first 0*field 0*field 1^2) =
      (field 0*field 1^2)*seed 0+secondB+(2 : ℂ) • secondWord := by
    simp [secondB,secondWord,pow_two,seed,first,
      MvPolynomial.smul_eq_C_mul]
    norm_num only [map_ofNat]
    ring
  rw [he,map_add,map_add,equation_multiple,zero_add,map_smul] at hd
  exact (eq_neg_of_add_eq_zero_left hd).trans (by simp)

theorem secondD_relation : q secondD = (-2 : ℂ) • q secondWord := by
  have hd := derivative_zero (field 0^2*first 1*field 1)
  have he : D () (field 0^2*first 1*field 1) =
      (field 0^2*field 1)*seed 1+secondD+(2 : ℂ) • secondWord := by
    simp [secondD,secondWord,pow_two,seed,first,
      MvPolynomial.smul_eq_C_mul]
    norm_num only [map_ofNat]
    ring
  rw [he,map_add,map_add,equation_multiple,zero_add,map_smul] at hd
  exact (eq_neg_of_add_eq_zero_left hd).trans (by simp)

theorem secondA_zero : q (monomial Second.a 1) = 0 := by
  have he : (monomial Second.a 1 : A) = (field 0*field 1^2)*seed 0 := by
    rw [Second.a,monomial_add_single,monomial_add_single,← X_pow_eq_monomial]
    simp [seed,first,field,index,shift,← Finsupp.single_add]
    ring
  rw [he]
  exact equation_multiple _ _

theorem secondE_zero : q (monomial Second.e 1) = 0 := by
  have he : (monomial Second.e 1 : A) = (field 0^2*field 1)*seed 1 := by
    rw [Second.e,monomial_add_single,monomial_add_single,← X_pow_eq_monomial]
    simp [seed,first,field,index,shift,← Finsupp.single_add]
  rw [he]
  exact equation_multiple _ _

theorem second_monomial_reconstruction {v : J →₀ ℕ}
    (ha : Finsupp.weight weight v = (4,2))
    (hr : Finsupp.weight speciesWeight v = 2) (c : ℂ) :
    q (monomial v c) = secondFunctional (monomial v c) • q secondWord := by
  have hm : (monomial v c : A) = c • monomial v 1 := by simp [smul_monomial]
  rw [hm,map_smul,map_smul]
  simp only [smul_eq_mul]
  rcases Second.classify ha hr with h | h | h | h | h
  · subst v
    have hf := second_annihilates ((Submodule.Quotient.mk_eq_zero _).mp secondA_zero)
    change secondFunctional (monomial Second.a 1) = 0 at hf
    rw [hf,secondA_zero]
    simp
  · rw [h,← secondB_monomial,secondB_value,secondB_relation]
    simp [smul_smul]
  · rw [h,← secondWord_monomial,second_value]
    simp
  · rw [h,← secondD_monomial,secondD_value,secondD_relation]
    simp [smul_smul]
  · subst v
    have hf := second_annihilates ((Submodule.Quotient.mk_eq_zero _).mp secondE_zero)
    change secondFunctional (monomial Second.e 1) = 0 at hf
    rw [hf,secondE_zero]
    simp

theorem second_reconstruction (p : source 1 2) :
    q p.val = secondFunctional p.val • q secondWord := by
  apply from_monomials (source 1 2) secondFunctional secondWord _ p
  intro p v hv
  have hn := MvPolynomial.mem_support_iff.mp hv
  exact second_monomial_reconstruction (p.property.1 hn) (p.property.2 hn) _

namespace Line
variable (V : Submodule ℂ A) (g : V) (f : A →ₗ[ℂ] ℂ)
  (hT : T ≤ f.ker) (hg : f g.val = 1)
  (hspan : ∀ p : V, q p.val = f p.val • q g.val)

def selected := input.select V (fun _ => le_refl _)
def coefficient : (selected V).Coefficient := ⟨{
  toLinearMap := f.comp V.subtype
  isIntertwining' _ := rfl },fun _ hp => hT hp⟩

include hspan in
theorem determined (F : (selected V).Coefficient) (p : V) : F.val p = f p.val*F.val g := by
  have hd : q (p.val-f p.val • g.val) = 0 := by
    rw [map_sub,map_smul,hspan p,sub_self]
  have ht : p-f p.val • g ∈ (selected V).relations := by
    change p.val-f p.val • g.val ∈ T
    exact (Submodule.Quotient.mk_eq_zero T).mp hd
  have hv := F.property ht
  change F.val (p-f p.val • g) = 0 at hv
  rw [map_sub,map_smul] at hv
  exact sub_eq_zero.mp hv

def equivalence : (selected V).Coefficient ≃ₗ[ℂ] ℂ where
  toFun F := F.val g
  invFun c := c • coefficient V f hT
  left_inv F := by
    apply Subtype.ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro p
    change F.val g*f p.val = F.val p
    rw [determined V g f hspan F p,mul_comm]
  right_inv c := by
    change c*f g.val = c
    rw [hg,mul_one]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include hT hg in
theorem image_nonzero : q g.val ≠ 0 := by
  intro hz
  let L : input.Source →ₗ[ℂ] ℂ := T.liftQ f hT
  have he : f g.val = 0 := calc
    f g.val = L (q g.val) := rfl
    _ = L 0 := congrArg L hz
    _ = 0 := L.map_zero
  rw [hg] at he
  exact one_ne_zero he

abbrev Image := input.selectedImage V
def imageGenerator : Image V := ⟨q g.val,⟨g,rfl⟩⟩
def imageCoordinate : Image V →ₗ[ℂ] ℂ :=
  (T.liftQ f hT).comp (Image V).subtype

include hspan in
theorem image_reconstruction (x : Image V) :
    x = imageCoordinate V f hT x • imageGenerator V g := by
  obtain ⟨p,hp⟩ := x.property
  apply Subtype.ext
  change x.val = (T.liftQ f hT) x.val • q g.val
  change q p.val = x.val at hp
  rw [← hp]
  exact hspan p

def imageEquiv : Image V ≃ₗ[ℂ] ℂ where
  toLinearMap := imageCoordinate V f hT
  invFun c := c • imageGenerator V g
  left_inv x := (image_reconstruction V g f hT hspan x).symm
  right_inv c := by
    change imageCoordinate V f hT (c • imageGenerator V g) = c
    rw [map_smul]
    change c • f g.val = c
    rw [hg,smul_eq_mul,mul_one]

end Line

def firstGenerator (r : Fin 2) : source r.val 1 := ⟨firstWord r.val,by
  rw [firstWord_monomial]
  constructor
  · apply isWeightedHomogeneous_monomial
    simp [firstA,weight,order_index,Finsupp.weight_single]
    omega
  · apply isWeightedHomogeneous_monomial
    simp [firstA,speciesWeight_index,Finsupp.weight_single]⟩

def secondGenerator : source 1 2 := ⟨secondWord,by
  rw [secondWord_monomial]
  constructor
  · apply isWeightedHomogeneous_monomial
    simp [Second.c,weight,order_index,Finsupp.weight_single]
  · apply isWeightedHomogeneous_monomial
    simp [Second.c,speciesWeight_index,Finsupp.weight_single]⟩

def firstEquiv (r : Fin 2) : (Line.selected (source r.val 1)).Coefficient ≃ₗ[ℂ] ℂ :=
  Line.equivalence (source r.val 1) (firstGenerator r) (firstFunctional r.val)
    (first_annihilates r.val) (first_value r.val) (first_reconstruction r)

def secondEquiv : (Line.selected (source 1 2)).Coefficient ≃ₗ[ℂ] ℂ :=
  Line.equivalence (source 1 2) secondGenerator secondFunctional
    second_annihilates second_value second_reconstruction

def firstImageEquiv (r : Fin 2) : Line.Image (source r.val 1) ≃ₗ[ℂ] ℂ :=
  Line.imageEquiv (source r.val 1) (firstGenerator r) (firstFunctional r.val)
    (first_annihilates r.val) (first_value r.val) (first_reconstruction r)

def secondImageEquiv : Line.Image (source 1 2) ≃ₗ[ℂ] ℂ :=
  Line.imageEquiv (source 1 2) secondGenerator secondFunctional
    second_annihilates second_value second_reconstruction

theorem first_image_dimension (r : Fin 2) : Module.finrank ℂ (Line.Image (source r.val 1)) = 1 := by
  rw [(firstImageEquiv r).finrank_eq]
  exact Module.finrank_self ℂ
theorem second_image_dimension : Module.finrank ℂ (Line.Image (source 1 2)) = 1 := by
  rw [secondImageEquiv.finrank_eq]
  exact Module.finrank_self ℂ

theorem first_dimension (r : Fin 2) :
    Module.finrank ℂ (Line.selected (source r.val 1)).Coefficient = 1 := by
  rw [(firstEquiv r).finrank_eq]
  exact Module.finrank_self ℂ

theorem second_dimension : Module.finrank ℂ (Line.selected (source 1 2)).Coefficient = 1 := by
  rw [secondEquiv.finrank_eq]
  exact Module.finrank_self ℂ

theorem first_nonzero (r : Fin 2) : q (firstWord r.val) ≠ 0 :=
  Line.image_nonzero (source r.val 1) (firstGenerator r) (firstFunctional r.val)
    (first_annihilates r.val) (first_value r.val)
theorem second_nonzero : q secondWord ≠ 0 :=
  Line.image_nonzero (source 1 2) secondGenerator secondFunctional second_annihilates second_value

def firstGlobal (r : Fin 2) : input.Coefficient := ⟨{
  toLinearMap := firstFunctional r.val
  isIntertwining' _ := rfl },fun _ hp => first_annihilates r.val hp⟩
def secondGlobal : input.Coefficient := ⟨{
  toLinearMap := secondFunctional
  isIntertwining' _ := rfl },fun _ hp => second_annihilates hp⟩

theorem first_global_value (r : Fin 2) (c : ℂ) :
    (c • firstGlobal r).val (firstWord r.val) = c := by
  change c*firstFunctional r.val (firstWord r.val) = c
  rw [first_value,mul_one]
theorem second_global_value (c : ℂ) : (c • secondGlobal).val secondWord = c := by
  change c*secondFunctional secondWord = c
  rw [second_value,mul_one]

@[simp] theorem first_extraction (r : Fin 2) (F : (Line.selected (source r.val 1)).Coefficient) :
    firstEquiv r F = F.val (firstGenerator r) := rfl
@[simp] theorem second_extraction (F : (Line.selected (source 1 2)).Coefficient) :
    secondEquiv F = F.val secondGenerator := rfl

end
end Math.ScalarTwoSpeciesCompleteness
