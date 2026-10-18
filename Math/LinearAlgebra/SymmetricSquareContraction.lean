import Math.LinearAlgebra.TensorSquareQuotients
import Math.LinearAlgebra.SectionKernel
import Mathlib.LinearAlgebra.Trace

/-! The symmetric-square contraction and its canonical section. The
trace-free summand is an actual kernel, uniformly in the ambient dimension. -/
namespace Math.SymmetricSquareContraction
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open TensorSquareQuotients
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {A : Type*} [AddCommGroup A] [Module ℂ A]
abbrev Source := (Sym[ℂ]^2 A) ⊗[ℂ] Module.Dual ℂ A
abbrev Pair := A ⊗[ℂ] Module.Dual ℂ A
@[reducible] local instance : AddCommGroup (Source (A := A)) := inferInstance

def evaluateLast : ((A ⊗[ℂ] A) ⊗[ℂ] Module.Dual ℂ A) →ₗ[ℂ] A :=
  (TensorProduct.rid ℂ A).toLinearMap.comp
    ((TensorProduct.map LinearMap.id (contractRight ℂ A)).comp
      (TensorProduct.assoc ℂ A A (Module.Dual ℂ A)).toLinearMap)

def contract : Source (A := A) →ₗ[ℂ] A :=
  evaluateLast.comp (TensorProduct.map symmetricSection LinearMap.id)

@[simp] theorem contract_pure (a b : A) (f : Module.Dual ℂ A) :
    contract (sym (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] f)=f b • a+f a • b := by
  simp only [contract, evaluateLast, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, symmetricSection_pure, TensorProduct.add_tmul, map_add,
    LinearEquiv.coe_coe, TensorProduct.assoc_tmul]
  rfl

def insertPair : ((Pair (A := A)) ⊗[ℂ] A) →ₗ[ℂ] Source (A := A) :=
  (TensorProduct.map sym LinearMap.id).comp
    ((TensorProduct.assoc ℂ A A (Module.Dual ℂ A)).symm.toLinearMap.comp
      ((TensorProduct.map LinearMap.id (TensorProduct.comm ℂ (Module.Dual ℂ A) A).toLinearMap).comp
        (TensorProduct.assoc ℂ A (Module.Dual ℂ A) A).toLinearMap))

@[simp] theorem insertPair_pure (a b : A) (f : Module.Dual ℂ A) :
    insertPair ((a ⊗ₜ[ℂ] f) ⊗ₜ[ℂ] b)=sym (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] f := rfl

variable [FiniteDimensional ℂ A]

def pairEnd : Pair (A := A) ≃ₗ[ℂ] Module.End ℂ A :=
  (TensorProduct.comm ℂ A (Module.Dual ℂ A)).trans (dualTensorHomEquiv ℂ A A)

@[simp] theorem pairEnd_pure (a : A) (f : Module.Dual ℂ A) :
    pairEnd (a ⊗ₜ[ℂ] f)=f.smulRight a := rfl

theorem contract_insertPair (p : Pair (A := A)) (a : A) :
    contract (insertPair (p ⊗ₜ[ℂ] a))=
      (pairEnd p) a+LinearMap.trace ℂ A (pairEnd p) • a := by
  induction p using TensorProduct.inductionOn with
  | add p q hp hq =>
    simp only [TensorProduct.add_tmul, map_add, hp, hq, LinearMap.add_apply, add_smul]
    module
  | tmul b f => rw [insertPair_pure, contract_pure, pairEnd_pure, LinearMap.trace_smulRight]; rfl

def coevaluation : Pair (A := A) := pairEnd.symm LinearMap.id

def sectionMap : A →ₗ[ℂ] Source (A := A) :=
  ((Module.finrank ℂ A : ℂ)+1)⁻¹ • insertPair.comp
    (TensorProduct.mk ℂ _ _ coevaluation)

theorem contract_section (a : A) : contract (sectionMap a)=a := by
  have hn : ((Module.finrank ℂ A : ℂ)+1)≠0 := by
    exact_mod_cast (Nat.succ_ne_zero (Module.finrank ℂ A))
  simp only [sectionMap, LinearMap.smul_apply, LinearMap.comp_apply, TensorProduct.mk_apply, map_smul,
    contract_insertPair, coevaluation, LinearEquiv.apply_symm_apply, LinearMap.id_apply,
    LinearMap.trace_id]
  rw [show a+(Module.finrank ℂ A : ℂ) • a=((Module.finrank ℂ A : ℂ)+1) • a by module,
    smul_smul, inv_mul_cancel₀ hn, one_smul]

abbrev Kernel := LinearMap.ker (contract (A := A))

def project : Source (A := A) →ₗ[ℂ] Kernel (A := A) :=
  SectionKernel.project contract sectionMap contract_section

def equivalence : Source (A := A) ≃ₗ[ℂ] A × Kernel (A := A) :=
  SectionKernel.equivalence contract sectionMap contract_section

/-- A nonzero square in a direction killed by a nonzero covector gives
an actual nonzero contraction-kernel vector. No dimension is evaluated. -/
theorem exists_kernel_ne_zero (a : A) (f : Module.Dual ℂ A)
    (ha : a≠0) (hf : f≠0) (hfa : f a=0) : ∃ x : Kernel (A := A), x≠0 := by
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_eq_one ℂ ha
  let F : Sym[ℂ]^2 A →ₗ[ℂ] ℂ := symmetricLift
    ((TensorProduct.lid ℂ ℂ).toLinearMap.comp (TensorProduct.map g g)) (by
      intro x y
      change g y*g x=g x*g y
      ring)
  have hF : F (sym (a ⊗ₜ[ℂ] a))=1 := by
    rw [show F (sym (a ⊗ₜ[ℂ] a))=g a*g a from symmetricLift_pure _ _ a a,
      hg, mul_one]
  let x : Kernel (A := A) := ⟨sym (a ⊗ₜ[ℂ] a) ⊗ₜ[ℂ] f, by
    rw [LinearMap.mem_ker, contract_pure, hfa, zero_smul, add_zero]⟩
  refine ⟨x, ?_⟩
  intro h
  have ht : sym (a ⊗ₜ[ℂ] a) ⊗ₜ[ℂ] f=0 := congrArg Subtype.val h
  have hz := congrArg
    (fun z => (TensorProduct.lid ℂ (Module.Dual ℂ A)) (TensorProduct.map F LinearMap.id z)) ht
  change F (sym (a ⊗ₜ[ℂ] a)) • f=0 at hz
  rw [hF, one_smul] at hz
  exact hf hz

end
end Math.SymmetricSquareContraction
