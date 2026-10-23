import Physics.FieldTheory.Jets.Weyl.Equations.PairedWeylInput

/-! Generated paired kinetic input and inverse coefficient transport. -/
namespace Physics.PairedWeylInput
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear Math.JetDirections PairedWeylKinetic
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

theorem oddInc_X (c : Bool) (a : Fin 2) (i : Fin 4) :
    oddInc c (ofSymbols a (MvPolynomial.X i)) = D i (psi c a) := by
  have he : (MvPolynomial.X i : Symbols (Fin 4)) =
      MvPolynomial.monomial (Finsupp.single i 1) 1 := rfl
  rw [he,ofSymbols_monomial]
  change JetFunctor.oddVector (jetInc c _) = _
  rw [jetInc_single,JetFunctor.oddVector_single,one_smul]
  simp [psi,D,LocalPolynomial.D,ScalarJetAlgebra.shift]

theorem left_row (a : Fin 2) : leftSeed (WeylLinearEquation.row a) = left a := by
  change oddInc false (WeylLinearEquation.seed (WeylLinearEquation.row a)) = _
  fin_cases a <;> dsimp only
  · change oddInc false (WeylLinearEquation.seed (WeylLinearEquation.row 0)) = left 0
    rw [WeylLinearEquation.seed_row_zero]
    simp [map_add,map_smul,oddInc_X,left,add_assoc]
  · change oddInc false (WeylLinearEquation.seed (WeylLinearEquation.row 1)) = left 1
    rw [WeylLinearEquation.seed_row_one]
    simp [map_add,map_smul,oddInc_X,left,sub_eq_add_neg,add_assoc]

theorem right_row (a : Fin 2) : rightSeed (WeylLinearEquation.row a) = right a := by
  change oddInc true (ConjugateWeylEquation.rightSeed (WeylLinearEquation.row a)) = _
  fin_cases a <;> dsimp only
  · change oddInc true (ConjugateWeylEquation.rightSeed (WeylLinearEquation.row 0)) = right 0
    rw [ConjugateWeylEquation.rightSeed_row_zero]
    simp [map_add,map_smul,oddInc_X,right,sub_eq_add_neg,add_assoc]
  · change oddInc true (ConjugateWeylEquation.rightSeed (WeylLinearEquation.row 1)) = right 1
    rw [ConjugateWeylEquation.rightSeed_row_one]
    simp [map_add,map_smul,oddInc_X,right,sub_eq_add_neg,add_assoc]

theorem equation_expansion (f : WeylLinearEquation.Equations) :
    f = f (Pi.single 0 1) • WeylLinearEquation.row 0 +
      f (Pi.single 1 1) • WeylLinearEquation.row 1 := by
  apply LinearMap.ext
  intro v
  have hv : v = v 0 • Pi.single 0 (1:ℂ)+v 1 • Pi.single 1 (1:ℂ) := by
    ext i; fin_cases i <;> simp
  conv_lhs => rw [hv,map_add,map_smul,map_smul]
  simp [WeylLinearEquation.row,smul_eq_mul,mul_comm]

theorem left_mem_span (f : WeylLinearEquation.Equations) : leftSeed f ∈ Submodule.span ℂ seeds := by
  apply TwoSidedCovariance.linear_two_mem leftSeed (Submodule.span ℂ seeds)
    f (WeylLinearEquation.row 0) (WeylLinearEquation.row 1) _ _ (equation_expansion f)
  · exact Submodule.subset_span ⟨(false,0),(seed_false 0).trans (left_row 0).symm⟩
  · exact Submodule.subset_span ⟨(false,1),(seed_false 1).trans (left_row 1).symm⟩

theorem right_mem_span (f : WeylLinearEquation.Equations) : rightSeed f ∈ Submodule.span ℂ seeds := by
  apply TwoSidedCovariance.linear_two_mem rightSeed (Submodule.span ℂ seeds)
    f (WeylLinearEquation.row 0) (WeylLinearEquation.row 1) _ _ (equation_expansion f)
  · exact Submodule.subset_span ⟨(true,0),(seed_true 0).trans (right_row 0).symm⟩
  · exact Submodule.subset_span ⟨(true,1),(seed_true 1).trans (right_row 1).symm⟩

theorem component_mem_span (j : Label) : seed j ∈ Submodule.span ℂ equations := by
  obtain ⟨c,a⟩ := j
  cases c
  · exact Submodule.subset_span (Or.inl ⟨WeylLinearEquation.row a,(left_row a).trans (seed_false a).symm⟩)
  · exact Submodule.subset_span (Or.inr ⟨WeylLinearEquation.row a,(right_row a).trans (seed_true a).symm⟩)

theorem equation_span : Submodule.span ℂ equations = Submodule.span ℂ seeds := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro p (⟨f,rfl⟩ | ⟨f,rfl⟩)
    · exact left_mem_span f
    · exact right_mem_span f
  · apply Submodule.span_le.mpr
    rintro p ⟨j,rfl⟩
    exact component_mem_span j

theorem closure_equal : TwoSidedDifferential.relations D equations =
    TwoSidedDifferential.relations D seeds := TwoSidedDifferential.relations_eq_of_span D equation_span

theorem generated_relations : density.relations = direct.relations := by
  rw [PairedWeylKinetic.relations_equal]
  change TwoSidedDifferential.relations D seeds ⊔ _ =
    TwoSidedDifferential.relations D equations ⊔ _
  rw [closure_equal]

def generated := density.input action (by
  rw [generated_relations]
  exact stable)

def toDirect (f : generated.Coefficient) : direct.Coefficient := ⟨f.val,by
  intro p hp
  apply f.property
  change p ∈ density.relations
  rw [generated_relations]
  exact hp⟩
def toGenerated (f : direct.Coefficient) : generated.Coefficient := ⟨f.val,by
  intro p hp
  apply f.property
  change p ∈ direct.relations
  rw [← generated_relations]
  exact hp⟩
def coefficientEquiv : generated.Coefficient ≃ₗ[ℂ] direct.Coefficient where
  toFun := toDirect
  invFun := toGenerated
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evaluation_agrees (f : generated.Coefficient) (p : A) :
    (coefficientEquiv f).val p = f.val p := rfl

theorem seed_zero (f : direct.Coefficient) (e : WeylLinearEquation.Equations) :
    f.val (leftSeed e) = 0 ∧ f.val (rightSeed e) = 0 :=
  ⟨f.property (TwoSidedDifferential.combined_seed _ _ (Or.inl ⟨_,rfl⟩)),
   f.property (TwoSidedDifferential.combined_seed _ _ (Or.inr ⟨_,rfl⟩))⟩

theorem current_ibp (f : direct.Coefficient) (i : Fin 4) (p q : A) :
    f.val (p*D i q) = -f.val (D i p*q) := by
  have hm : D i (p*q) ∈ direct.relations :=
    Submodule.mem_sup_right ⟨Finsupp.single i (p*q),VariationalIBP.divergence_single D i (p*q)⟩
  have hz := f.property hm
  change f.val (D i (p*q)) = 0 at hz
  rw [MixedJetAlgebra.totalDerivative_mul,map_add] at hz
  exact eq_neg_of_add_eq_zero_right hz

theorem candidate_extraction (f : generated.Coefficient) :
    generated.coefficientEquiv f (generated.projection DerivativeLiteratureMixed.candidate) =
      direct.coefficientEquiv (toDirect f) (direct.projection DerivativeLiteratureMixed.candidate) := rfl
end
end Physics.PairedWeylInput
