import Math.LinearAlgebra.Symmetric.SymmetricSquareContraction
import Math.RepresentationTheory.Symmetric.SymmetricPowerOperations

/-! The symmetric-square/dual-square partial trace has a canonical
section. The proof is by universal rank-one identities, without choosing
or expanding a basis. -/
namespace Math.SymmetricSquarePartialTrace
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open TensorSquareQuotients
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {A : Type*} [AddCommGroup A] [Module ℂ A]
abbrev D := Module.Dual ℂ A
abbrev Pair := A ⊗[ℂ] D (A := A)
abbrev Source := (Sym[ℂ]^2 A) ⊗[ℂ] Sym[ℂ]^2 (D (A := A))
@[reducible] local instance : AddCommGroup (Source (A := A)) := inferInstance

def contract : Source (A := A) →ₗ[ℂ] Pair (A := A) :=
  (TensorProduct.lid ℂ (Pair (A := A))).toLinearMap.comp
    ((TensorProduct.map (contractRight ℂ A) LinearMap.id).comp
      ((TensorProduct.tensorTensorTensorComm ℂ A A (D (A := A)) (D (A := A))).toLinearMap.comp
        (TensorProduct.map symmetricSection symmetricSection)))

@[simp] theorem contract_pure (a b : A) (f g : D (A := A)) :
    contract (sym (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] sym (f ⊗ₜ[ℂ] g))=
      f a • (b ⊗ₜ[ℂ] g)+g a • (b ⊗ₜ[ℂ] f)+
        (f b • (a ⊗ₜ[ℂ] g)+g b • (a ⊗ₜ[ℂ] f)) := by
  simp only [contract, LinearMap.comp_apply, TensorProduct.map_tmul,
    symmetricSection_pure, TensorProduct.add_tmul, TensorProduct.tmul_add, map_add]
  change f a • (b ⊗ₜ[ℂ] g)+f b • (a ⊗ₜ[ℂ] g)+
      (g a • (b ⊗ₜ[ℂ] f)+g b • (a ⊗ₜ[ℂ] f))=_
  abel

def insertPair : (Pair (A := A) ⊗[ℂ] Pair (A := A)) →ₗ[ℂ] Source (A := A) :=
  (TensorProduct.map sym sym).comp
    (TensorProduct.tensorTensorTensorComm ℂ A (D (A := A)) A (D (A := A))).toLinearMap

@[simp] theorem insertPair_pure (a b : A) (f g : D (A := A)) :
    insertPair ((a ⊗ₜ[ℂ] f) ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] g))=
      sym (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] sym (f ⊗ₜ[ℂ] g) := rfl

/-- A vector/covector pair with zero pairing gives a nonzero pure
partial-trace-kernel vector, proved by two scalar evaluations. -/
theorem exists_kernel_ne_zero (a : A) (f : D (A := A))
    (ha : a≠0) (hf : f≠0) (hfa : f a=0) :
    ∃ x : LinearMap.ker (contract (A := A)), x≠0 := by
  obtain ⟨g,hg⟩ := Module.Projective.exists_dual_eq_one ℂ ha
  obtain ⟨h,hh⟩ := Module.Projective.exists_dual_eq_one ℂ hf
  let F := SymmetricPowerOperations.powerEval 2 g
  let H := SymmetricPowerOperations.powerEval 2 h
  have hF : F (sym (a ⊗ₜ[ℂ] a))=1 := by
    simp [F, sym_tmul, SymmetricPowerOperations.powerEval_pure, Fin.prod_univ_succ, hg]
  have hH : H (sym (f ⊗ₜ[ℂ] f))=1 := by
    simp [H, sym_tmul, SymmetricPowerOperations.powerEval_pure, Fin.prod_univ_succ, hh]
  let x : LinearMap.ker (contract (A := A)) :=
    ⟨sym (a ⊗ₜ[ℂ] a) ⊗ₜ[ℂ] sym (f ⊗ₜ[ℂ] f), by
      rw [LinearMap.mem_ker, contract_pure, hfa, zero_smul, add_zero, add_zero]⟩
  refine ⟨x, ?_⟩
  intro hx
  have ht : sym (a ⊗ₜ[ℂ] a) ⊗ₜ[ℂ] sym (f ⊗ₜ[ℂ] f)=0 := congrArg Subtype.val hx
  have hz := congrArg (fun z => (TensorProduct.lid ℂ ℂ) (TensorProduct.map F H z)) ht
  change F (sym (a ⊗ₜ[ℂ] a))*H (sym (f ⊗ₜ[ℂ] f))=0 at hz
  rw [hF, hH, mul_one] at hz
  exact one_ne_zero hz

variable [FiniteDimensional ℂ A]
abbrev pairEnd := SymmetricSquareContraction.pairEnd (A := A)
abbrev coevaluation := SymmetricSquareContraction.coevaluation (A := A)

theorem contract_insert_left (a : A) (f : D (A := A)) (q : Pair (A := A)) :
    contract (insertPair ((a ⊗ₜ[ℂ] f) ⊗ₜ[ℂ] q))=
      f a • q+((pairEnd q) a ⊗ₜ[ℂ] f)+
        (a ⊗ₜ[ℂ] f.comp (pairEnd q))+LinearMap.trace ℂ A (pairEnd q) • (a ⊗ₜ[ℂ] f) := by
  induction q using TensorProduct.inductionOn with
  | add q u hq hu =>
    simp only [TensorProduct.tmul_add, map_add, hq, hu, LinearMap.add_apply,
      LinearMap.comp_add, TensorProduct.add_tmul, TensorProduct.tmul_add, smul_add, add_smul]
    module
  | tmul b g =>
    rw [insertPair_pure, contract_pure, SymmetricSquareContraction.pairEnd_pure,
      LinearMap.trace_smulRight]
    have he : f.comp (g.smulRight b)=f b • g := by ext x; simp [mul_comm]
    rw [he]
    simp only [LinearMap.smulRight_apply, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    module

def insert : Pair (A := A) →ₗ[ℂ] Source (A := A) :=
  insertPair.comp ((TensorProduct.mk ℂ _ _).flip coevaluation)

theorem contract_insert (p : Pair (A := A)) :
    contract (insert p)=((Module.finrank ℂ A : ℂ)+2) • p+
      LinearMap.trace ℂ A (pairEnd p) • coevaluation := by
  induction p using TensorProduct.inductionOn with
  | add p q hp hq =>
    simp only [map_add, hp, hq, smul_add, add_smul]
    module
  | tmul a f =>
    change contract (insertPair ((a ⊗ₜ[ℂ] f) ⊗ₜ[ℂ] coevaluation))=_
    rw [contract_insert_left]
    simp only [coevaluation, SymmetricSquareContraction.coevaluation,
      LinearEquiv.apply_symm_apply, LinearMap.id_apply, LinearMap.comp_id,
      LinearMap.trace_id, SymmetricSquareContraction.pairEnd_pure, LinearMap.trace_smulRight]
    module

def correct : Pair (A := A) →ₗ[ℂ] Pair (A := A) :=
  ((Module.finrank ℂ A : ℂ)+2)⁻¹ •
    (LinearMap.id-((2 : ℂ)*(Module.finrank ℂ A : ℂ)+2)⁻¹ •
      ((LinearMap.trace ℂ A).comp pairEnd.toLinearMap).smulRight coevaluation)

theorem contract_insert_correct (p : Pair (A := A)) : contract (insert (correct p))=p := by
  have hn : ((Module.finrank ℂ A : ℂ)+2)≠0 := by
    exact_mod_cast (show Module.finrank ℂ A+2≠0 by omega)
  have hd : ((2 : ℂ)*(Module.finrank ℂ A : ℂ)+2)≠0 := by
    exact_mod_cast (show 2*Module.finrank ℂ A+2≠0 by omega)
  rw [contract_insert]
  simp only [correct, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, LinearMap.comp_apply, map_smul, map_sub,
    smul_eq_mul, coevaluation,
    SymmetricSquareContraction.coevaluation, LinearEquiv.apply_symm_apply, LinearMap.trace_id]
  match_scalars
  all_goals field_simp [hn, hd]
  all_goals ring

def sectionMap : Pair (A := A) →ₗ[ℂ] Source (A := A) := insert.comp correct

theorem contract_section (p : Pair (A := A)) : contract (sectionMap p)=p :=
  contract_insert_correct p

abbrev Kernel := LinearMap.ker (contract (A := A))

def project : Source (A := A) →ₗ[ℂ] Kernel (A := A) :=
  SectionKernel.project contract sectionMap contract_section

def equivalence : Source (A := A) ≃ₗ[ℂ] Pair (A := A) × Kernel (A := A) :=
  SectionKernel.equivalence contract sectionMap contract_section

end
end Math.SymmetricSquarePartialTrace
