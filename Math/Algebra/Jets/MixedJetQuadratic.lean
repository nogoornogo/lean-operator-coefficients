import Math.RepresentationTheory.Jets.MixedJetIBP
import Math.Algebra.Jets.ScalarJetQuadratic
import Math.Algebra.Jets.MixedJetPairCoordinates

/-! A complete mixed IBP quotient with two odd fields, one even field and
two derivatives. The Pauli cancellation and relation are computed in the
actual exterior/polynomial algebra. -/
namespace Math.MixedJetQuadratic
set_option autoImplicit false
noncomputable section
open MixedJetAlgebra
open scoped TensorProduct

abbrev Ambient := Algebra Unit Unit Unit
abbrev Source := grade Unit Unit Unit 2 1 2
abbrev Primitive := grade Unit Unit Unit 2 1 1
abbrev jetIndex := ScalarJetQuadratic.jetIndex

@[reducible] local instance : AddCommGroup Ambient := inferInstance
@[reducible] local instance : Module ℂ Ambient := inferInstance
@[reducible] local instance : AddCommGroup Source := inferInstance
@[reducible] local instance : Module ℂ Source := inferInstance
@[reducible] local instance : AddCommGroup Primitive := inferInstance
@[reducible] local instance : Module ℂ Primitive := inferInstance

def psi (k : ℕ) : Odd Unit Unit := ExteriorAlgebra.ι ℂ (Finsupp.single (jetIndex k) 1)
def phi (k : ℕ) : Even Unit Unit := MvPolynomial.X (jetIndex k)
def raw (a b c : ℕ) : Ambient := (psi a * psi b) ⊗ₜ[ℂ] phi c

@[simp] theorem jetIndex_eq (a b : ℕ) : jetIndex a = jetIndex b ↔ a = b :=
  ScalarJetQuadratic.jetIndex_injective.eq_iff

@[simp] theorem raw_same (a c : ℕ) : raw a a c = 0 := by
  simp [raw, psi]

theorem raw_swap (a b c : ℕ) : raw b a c = -raw a b c := by
  have h : psi a * psi b + psi b * psi a = 0 := ExteriorAlgebra.ι_add_mul_swap _ _
  rw [raw, raw, eq_neg_of_add_eq_zero_right h, TensorProduct.neg_tmul]

theorem raw_mem (a b c : ℕ) : raw a b c ∈ grade Unit Unit Unit 2 1 (a + b + c) := by
  simpa [word, wordOrder, psi, phi, raw, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, ScalarJetAlgebra.order, ScalarJetQuadratic.jetIndex,
    Fin.sum_univ_succ, Fin.prod_univ_succ, Matrix.vecTail, Finsupp.weight_single] using
    word_mem ![jetIndex a, jetIndex b] ![jetIndex c]

def first : Source := ⟨raw 0 1 1, raw_mem 0 1 1⟩
def second : Source := ⟨raw 0 2 0, raw_mem 0 2 0⟩
def primitive : Primitive := ⟨raw 0 1 0, raw_mem 0 1 0⟩

theorem word_eq_raw (f : Fin 2 → ScalarJetAlgebra.Index Unit Unit)
    (b : Fin 1 → ScalarJetAlgebra.Index Unit Unit) :
    word f b = raw (ScalarJetAlgebra.order (f 0).2) (ScalarJetAlgebra.order (f 1).2)
      (ScalarJetAlgebra.order (b 0).2) := by
  have hf : f = ![jetIndex (ScalarJetAlgebra.order (f 0).2),
      jetIndex (ScalarJetAlgebra.order (f 1).2)] := by
    funext i
    fin_cases i
    · exact ScalarJetQuadratic.index_eq (f 0)
    · exact ScalarJetQuadratic.index_eq (f 1)
  have hb : b = ![jetIndex (ScalarJetAlgebra.order (b 0).2)] := by
    funext i
    fin_cases i
    exact ScalarJetQuadratic.index_eq (b 0)
  conv_lhs => rw [hf, hb]
  simp [word, psi, phi, raw, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, Matrix.vecTail]

theorem wordOrder_two_one (f : Fin 2 → ScalarJetAlgebra.Index Unit Unit)
    (b : Fin 1 → ScalarJetAlgebra.Index Unit Unit) :
    wordOrder f b = ScalarJetAlgebra.order (f 0).2 + ScalarJetAlgebra.order (f 1).2 +
      ScalarJetAlgebra.order (b 0).2 := by
  simp [wordOrder, Fin.sum_univ_succ]

theorem source_span_ambient : (grade Unit Unit Unit 2 1 2) =
    Submodule.span ℂ ({raw 0 1 1, raw 0 2 0} : Set Ambient) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨f, b, hf, rfl⟩
    rw [wordOrder_two_one] at hf
    rw [word_eq_raw]
    generalize ScalarJetAlgebra.order (f 0).2 = aa at *
    generalize ScalarJetAlgebra.order (f 1).2 = bb at *
    generalize ScalarJetAlgebra.order (b 0).2 = cc at *
    have h : (aa = 0 ∧ bb = 0 ∧ cc = 2) ∨ (aa = 0 ∧ bb = 1 ∧ cc = 1) ∨
        (aa = 0 ∧ bb = 2 ∧ cc = 0) ∨ (aa = 1 ∧ bb = 0 ∧ cc = 1) ∨
        (aa = 1 ∧ bb = 1 ∧ cc = 0) ∨ (aa = 2 ∧ bb = 0 ∧ cc = 0) := by omega
    rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
      ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    · simp
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · rw [raw_swap 0 1 1]; exact Submodule.neg_mem _ (Submodule.subset_span (by simp))
    · simp
    · rw [raw_swap 0 2 0]; exact Submodule.neg_mem _ (Submodule.subset_span (by simp))
  · apply Submodule.span_le.mpr
    intro p hp
    rcases hp with rfl | rfl
    · exact raw_mem 0 1 1
    · exact raw_mem 0 2 0

theorem primitive_span_ambient : (grade Unit Unit Unit 2 1 1) = ℂ ∙ raw 0 1 0 := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨f, b, hf, rfl⟩
    rw [wordOrder_two_one] at hf
    rw [word_eq_raw]
    generalize ScalarJetAlgebra.order (f 0).2 = aa at *
    generalize ScalarJetAlgebra.order (f 1).2 = bb at *
    generalize ScalarJetAlgebra.order (b 0).2 = cc at *
    have h : (aa = 0 ∧ bb = 0 ∧ cc = 1) ∨ (aa = 0 ∧ bb = 1 ∧ cc = 0) ∨
        (aa = 1 ∧ bb = 0 ∧ cc = 0) := by omega
    rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    · simp
    · exact Submodule.mem_span_singleton_self _
    · rw [raw_swap 0 1 0]; exact Submodule.neg_mem _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact raw_mem 0 1 0

theorem source_reconstruct (p : Source) : ∃ a b : ℂ, p = a • first + b • second := by
  have hp := p.property
  change p.val ∈ grade Unit Unit Unit 2 1 2 at hp
  rw [source_span_ambient] at hp
  obtain ⟨a,b,h⟩ := Submodule.mem_span_pair.mp hp
  exact ⟨a,b,Subtype.ext h.symm⟩

theorem primitive_reconstruct (p : Primitive) : ∃ c : ℂ, p = c • primitive := by
  have hp := p.property
  change p.val ∈ grade Unit Unit Unit 2 1 1 at hp
  rw [primitive_span_ambient] at hp
  obtain ⟨c,h⟩ := Submodule.mem_span_singleton.mp hp
  exact ⟨c,Subtype.ext h.symm⟩

theorem derivative_primitive : derivative () 2 1 1 primitive = first + second := by
  apply Subtype.ext
  change totalDerivative () (raw 0 1 0) = raw 0 1 1 + raw 0 2 0
  have hs (k : ℕ) : JetLinear.shift () (Finsupp.single (jetIndex k) 1) =
      Finsupp.single (jetIndex (k + 1)) 1 := by
    simp [ScalarJetAlgebra.shift, ScalarJetQuadratic.jetIndex]
  simp only [raw, totalDerivative_tmul, oddDerivative, psi,
    ExteriorAlgebra.derivationOfLinear_mul, ExteriorAlgebra.derivationOfLinear_ι, hs,
    phi, ScalarJetAlgebra.totalDerivative_X]
  have hshift : ScalarJetAlgebra.shift () (jetIndex 0) = jetIndex 1 := by
    simp [ScalarJetAlgebra.shift, ScalarJetQuadratic.jetIndex]
  rw [hshift]
  simp [add_comm]

theorem source_span : Submodule.span ℂ ({first, second} : Set Source) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨a,b,rfl⟩ := source_reconstruct p
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

def relations : Submodule ℂ Source := MixedJetIBP.relations (F := Unit) (B := Unit) (I := Unit) 2 1 1

theorem relations_span : relations =
    ℂ ∙ (first + second) := by
  apply le_antisymm
  · rintro p ⟨c, rfl⟩
    have hc : c = Finsupp.single () (c ()) := by
      apply Finsupp.ext
      intro i
      cases i
      simp
    obtain ⟨a,ha⟩ := primitive_reconstruct (c ())
    rw [hc, GradedJetIBP.divergence_single, ha, map_smul]
    change a • derivative () 2 1 1 primitive ∈ _
    rw [derivative_primitive]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_singleton_le_iff_mem, ← derivative_primitive]
    refine ⟨Finsupp.single () primitive, ?_⟩
    change Finsupp.lsum ℂ (fun i : Unit => derivative i 2 1 1)
      (Finsupp.single () primitive) = derivative () 2 1 1 primitive
    exact Finsupp.lsum_single ℂ _ () primitive

def coordinate (a b c : ℕ) : Ambient →ₗ[ℂ] ℂ :=
  TensorProduct.lift (((LinearMap.mul ℂ ℂ).compl₂
    (MvPolynomial.lcoeff ℂ (Finsupp.single (jetIndex c) 1))).comp
      (pairCoordinate (jetIndex a) (jetIndex b)))

def reduction : Source →ₗ[ℂ] ℂ :=
  ((coordinate 0 1 1) - (coordinate 0 2 0)).comp Source.subtype

@[simp] theorem reduction_first : reduction first = 1 := by
  simp [reduction, first, coordinate, raw, pairCoordinate_ι_mul, psi, phi]

@[simp] theorem reduction_second : reduction second = -1 := by
  simp [reduction, second, coordinate, raw, pairCoordinate_ι_mul, psi, phi]

theorem reduction_ker : reduction.ker = relations := by
  rw [relations_span]
  ext p
  constructor
  · intro hp
    obtain ⟨a,b,rfl⟩ := source_reconstruct p
    have hab : a = b := sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hp)
    rw [hab, ← smul_add]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · intro hp
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hp
    change reduction (a • (first + second)) = 0
    simp

theorem reduction_surjective : Function.Surjective reduction := by
  intro c
  exact ⟨c • first, by simp⟩

abbrev Quotient := Source ⧸ relations

def quotientEquiv : Quotient ≃ₗ[ℂ] ℂ :=
  (Submodule.quotEquivOfEq _ _ reduction_ker.symm).trans
    (reduction.quotKerEquivOfSurjective reduction_surjective)

@[simp] theorem quotientEquiv_mk (p : Source) :
    quotientEquiv (Submodule.Quotient.mk p) = reduction p := rfl

theorem quotient_finrank : Module.finrank ℂ Quotient = 1 := by
  rw [quotientEquiv.finrank_eq, Module.finrank_self]

theorem first_survives :
    relations.mkQ first ≠ 0 := by
  intro h
  have he := congrArg quotientEquiv h
  simp at he

theorem ibp_identity :
    relations.mkQ second = -relations.mkQ first := by
  apply quotientEquiv.injective
  simp

end
end Math.MixedJetQuadratic
