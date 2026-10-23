import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsFirstTensor

/-! The tensor words cover the whole mixed grade, including every derivative
allocation and both chiralities. No invariant spanning premise is assumed. -/
namespace Physics.WeylHiggsFirstSource
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear PairedWeylKinetic WeylHiggsInput WeylHiggsFirstTensor
open scoped TensorProduct
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

def markOrder : Fin 4 → Fin 4 → Fin 4 :=
  ![![0,1,2,3],![1,0,2,3],![2,0,1,3],![3,0,1,2]]

theorem first_odd (f : Fin 2 → Label) (b : Fin 4 → Label) (t : Fin 2) (i : Fin 4) :
    MixedFirstJetWords.first f b (.inl t) i =
      word (f 0).1 (f 1).1 b t.castSucc (Finsupp.single i 1)
        (Finsupp.single (f 0).2 1) (Finsupp.single (f 1).2 1) := by
  fin_cases t <;>
    simp [MixedFirstJetWords.first,MixedJetAlgebra.word,ExteriorAlgebra.ιMulti_succ_apply,
      Fin.prod_univ_succ,Matrix.vecTail,word,Math.MixedFirstJetTensor.word,
      evenField,rest,DerivativeLiteratureMixed.h,MixedJetAlgebra.even,psi,
      MixedJetAlgebra.odd,Math.MixedFirstJetTensor.directional_single,
      MixedJetAlgebra.oddDerivative,JetLinear.shift_single,ScalarJetAlgebra.shift,
      Algebra.TensorProduct.tmul_mul_tmul,mul_assoc]

private theorem first_even0 (f : Fin 2 → Label) (b : Fin 4 → Label) (i : Fin 4) :
    MixedFirstJetWords.first f b (.inr 0) i =
      word (f 0).1 (f 1).1 (b ∘ markOrder 0) 2 (Finsupp.single i 1)
        (Finsupp.single (f 0).2 1) (Finsupp.single (f 1).2 1) := by
  simp [MixedFirstJetWords.first,MixedJetAlgebra.word,ExteriorAlgebra.ιMulti_succ_apply,
    Fin.prod_univ_succ,Matrix.vecTail,word,Math.MixedFirstJetTensor.word,
    evenField,rest,DerivativeLiteratureMixed.h,MixedJetAlgebra.even,psi,
    MixedJetAlgebra.odd,Math.MixedFirstJetTensor.directional_single,
    MixedJetAlgebra.oddDerivative,ScalarJetAlgebra.shift,markOrder,
    Algebra.TensorProduct.tmul_mul_tmul]
  apply congrArg (fun p : DerivativeLiteratureHiggs.A =>
    (ExteriorAlgebra.ι ℂ (Finsupp.single (f 0,0) 1) *
      ExteriorAlgebra.ι ℂ (Finsupp.single (f 1,0) 1)) ⊗ₜ[ℂ] p)
  ring

private theorem first_even1 (f : Fin 2 → Label) (b : Fin 4 → Label) (i : Fin 4) :
    MixedFirstJetWords.first f b (.inr 1) i =
      word (f 0).1 (f 1).1 (b ∘ markOrder 1) 2 (Finsupp.single i 1)
        (Finsupp.single (f 0).2 1) (Finsupp.single (f 1).2 1) := by
  simp [MixedFirstJetWords.first,MixedJetAlgebra.word,ExteriorAlgebra.ιMulti_succ_apply,
    Fin.prod_univ_succ,Matrix.vecTail,word,Math.MixedFirstJetTensor.word,
    evenField,rest,DerivativeLiteratureMixed.h,MixedJetAlgebra.even,psi,
    MixedJetAlgebra.odd,Math.MixedFirstJetTensor.directional_single,
    MixedJetAlgebra.oddDerivative,ScalarJetAlgebra.shift,markOrder,
    Algebra.TensorProduct.tmul_mul_tmul]
  apply congrArg (fun p : DerivativeLiteratureHiggs.A =>
    (ExteriorAlgebra.ι ℂ (Finsupp.single (f 0,0) 1) *
      ExteriorAlgebra.ι ℂ (Finsupp.single (f 1,0) 1)) ⊗ₜ[ℂ] p)
  ring

private theorem first_even2 (f : Fin 2 → Label) (b : Fin 4 → Label) (i : Fin 4) :
    MixedFirstJetWords.first f b (.inr 2) i =
      word (f 0).1 (f 1).1 (b ∘ markOrder 2) 2 (Finsupp.single i 1)
        (Finsupp.single (f 0).2 1) (Finsupp.single (f 1).2 1) := by
  simp [MixedFirstJetWords.first,MixedJetAlgebra.word,ExteriorAlgebra.ιMulti_succ_apply,
    Fin.prod_univ_succ,Matrix.vecTail,word,Math.MixedFirstJetTensor.word,
    evenField,rest,DerivativeLiteratureMixed.h,MixedJetAlgebra.even,psi,
    MixedJetAlgebra.odd,Math.MixedFirstJetTensor.directional_single,
    MixedJetAlgebra.oddDerivative,ScalarJetAlgebra.shift,markOrder,
    Algebra.TensorProduct.tmul_mul_tmul]
  apply congrArg (fun p : DerivativeLiteratureHiggs.A =>
    (ExteriorAlgebra.ι ℂ (Finsupp.single (f 0,0) 1) *
      ExteriorAlgebra.ι ℂ (Finsupp.single (f 1,0) 1)) ⊗ₜ[ℂ] p)
  ring

private theorem first_even3 (f : Fin 2 → Label) (b : Fin 4 → Label) (i : Fin 4) :
    MixedFirstJetWords.first f b (.inr 3) i =
      word (f 0).1 (f 1).1 (b ∘ markOrder 3) 2 (Finsupp.single i 1)
        (Finsupp.single (f 0).2 1) (Finsupp.single (f 1).2 1) := by
  simp [MixedFirstJetWords.first,MixedJetAlgebra.word,ExteriorAlgebra.ιMulti_succ_apply,
    Fin.prod_univ_succ,Matrix.vecTail,word,Math.MixedFirstJetTensor.word,
    evenField,rest,DerivativeLiteratureMixed.h,MixedJetAlgebra.even,psi,
    MixedJetAlgebra.odd,Math.MixedFirstJetTensor.directional_single,
    MixedJetAlgebra.oddDerivative,ScalarJetAlgebra.shift,markOrder,
    Algebra.TensorProduct.tmul_mul_tmul]
  apply congrArg (fun p : DerivativeLiteratureHiggs.A =>
    (ExteriorAlgebra.ι ℂ (Finsupp.single (f 0,0) 1) *
      ExteriorAlgebra.ι ℂ (Finsupp.single (f 1,0) 1)) ⊗ₜ[ℂ] p)
  ring

theorem first_even (f : Fin 2 → Label) (b : Fin 4 → Label) (t i : Fin 4) :
    MixedFirstJetWords.first f b (.inr t) i =
      word (f 0).1 (f 1).1 (b ∘ markOrder t) 2 (Finsupp.single i 1)
        (Finsupp.single (f 0).2 1) (Finsupp.single (f 1).2 1) := by
  fin_cases t
  · exact first_even0 f b i
  · exact first_even1 f b i
  · exact first_even2 f b i
  · exact first_even3 f b i

def words : Set A := {p | ∃ (c d : Bool) (b : Fin 4 → Label) (r : Fin 3)
  (i : Fin 4) (a e : Fin 2), word c d b r (Finsupp.single i 1)
    (Finsupp.single a 1) (Finsupp.single e 1) = p}

theorem grade_le_span : V ≤ Submodule.span ℂ words := by
  change MixedJetAlgebra.grade Label Label (Fin 4) 2 4 1 ≤ _
  rw [Math.MixedFirstJetWords.grade_eq_span]
  apply Submodule.span_le.mpr
  rintro p ⟨f,b,t,i,rfl⟩
  cases t with
  | inl t =>
    rw [first_odd]
    exact Submodule.subset_span ⟨_,_,_,_,_,_,_,rfl⟩
  | inr t =>
    rw [first_even]
    exact Submodule.subset_span ⟨_,_,_,_,_,_,_,rfl⟩

theorem zero_of_words (f : A →ₗ[ℂ] ℂ)
    (h : ∀ c d b r i a e, f (word c d b r (Finsupp.single i 1)
      (Finsupp.single a 1) (Finsupp.single e 1)) = 0)
    (p : A) (hp : p ∈ V) : f p = 0 := by
  have hs : Submodule.span ℂ words ≤ f.ker := by
    apply Submodule.span_le.mpr
    rintro q ⟨c,d,b,r,i,a,e,rfl⟩
    exact h c d b r i a e
  exact hs (grade_le_span hp)

end
end Physics.WeylHiggsFirstSource
