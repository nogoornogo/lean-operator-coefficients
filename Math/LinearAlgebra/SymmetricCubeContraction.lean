import Math.LinearAlgebra.SymmetricCubeHook
import Math.LinearAlgebra.SymmetricSquareContraction
import Math.RepresentationTheory.SymmetricPowerOperations

/-! The cubic/dual contraction and its canonical coevaluation section.
The complement is an actual kernel; no color irreducibility or numerical
dimension is assumed or computed. -/
namespace Math.SymmetricCubeContraction
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open TensorSquareQuotients
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {A : Type*} [AddCommGroup A] [Module ℂ A]
abbrev Source := (Sym[ℂ]^3 A) ⊗[ℂ] Module.Dual ℂ A
abbrev Pair := SymmetricSquareContraction.Pair (A := A)
@[reducible] local instance : AddCommGroup (Source (A := A)) := inferInstance
@[reducible] local instance : AddCommGroup (Sym[ℂ]^2 A) :=
  Module.addCommMonoidToAddCommGroup ℂ

def switch : ((A ⊗[ℂ] Sym[ℂ]^2 A) ⊗[ℂ] Module.Dual ℂ A) ≃ₗ[ℂ]
    (Pair (A := A) ⊗[ℂ] Sym[ℂ]^2 A) :=
  (TensorProduct.assoc ℂ A (Sym[ℂ]^2 A) (Module.Dual ℂ A)).trans
    ((TensorProduct.congr (.refl ℂ A) (TensorProduct.comm ℂ _ _)).trans
      (TensorProduct.assoc ℂ A (Module.Dual ℂ A) (Sym[ℂ]^2 A)).symm)

def evaluateFirst : ((A ⊗[ℂ] Sym[ℂ]^2 A) ⊗[ℂ] Module.Dual ℂ A) →ₗ[ℂ] Sym[ℂ]^2 A :=
  (TensorProduct.lid ℂ (Sym[ℂ]^2 A)).toLinearMap.comp
    ((TensorProduct.map (contractRight ℂ A) LinearMap.id).comp switch.toLinearMap)

def contract : Source (A := A) →ₗ[ℂ] Sym[ℂ]^2 A :=
  evaluateFirst.comp (TensorProduct.map SymmetricCubeHook.coproduct LinearMap.id)

@[simp] theorem contract_pure (a b c : A) (f : Module.Dual ℂ A) :
    contract (SymmetricPower.tprod ℂ ![a,b,c] ⊗ₜ[ℂ] f)=
      f a • sym (b ⊗ₜ[ℂ] c)+f b • sym (a ⊗ₜ[ℂ] c)+f c • sym (a ⊗ₜ[ℂ] b) := by
  simp only [contract, evaluateFirst, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, SymmetricCubeHook.coproduct_pure, TensorProduct.add_tmul, map_add]
  rfl

theorem source_ext {N : Type*} [AddCommGroup N] [Module ℂ N]
    {f g : Source (A := A) →ₗ[ℂ] N}
    (h : ∀ a b c d, f (SymmetricPower.tprod ℂ ![a,b,c] ⊗ₜ[ℂ] d)=
      g (SymmetricPower.tprod ℂ ![a,b,c] ⊗ₜ[ℂ] d)) : f=g := by
  apply TensorProduct.ext'
  intro x d
  have hd : f.comp ((TensorProduct.mk ℂ _ _).flip d)=
      g.comp ((TensorProduct.mk ℂ _ _).flip d) := by
    apply SymmetricPower.ext
    intro v
    have hv : v=![v 0,v 1,v 2] := by ext i; fin_cases i <;> rfl
    change f (SymmetricPower.tprod ℂ v ⊗ₜ[ℂ] d)=g (SymmetricPower.tprod ℂ v ⊗ₜ[ℂ] d)
    rw [hv]
    exact h _ _ _ _
  exact LinearMap.congr_fun hd x

def insertPair : (Pair (A := A) ⊗[ℂ] Sym[ℂ]^2 A) →ₗ[ℂ] Source (A := A) :=
  (TensorProduct.map SymmetricCubeHook.multiply LinearMap.id).comp switch.symm.toLinearMap

@[simp] theorem insertPair_pure (a b c : A) (f : Module.Dual ℂ A) :
    insertPair ((a ⊗ₜ[ℂ] f) ⊗ₜ[ℂ] sym (b ⊗ₜ[ℂ] c))=
      SymmetricPower.tprod ℂ ![a,b,c] ⊗ₜ[ℂ] f := by
  change SymmetricCubeHook.multiply (a ⊗ₜ[ℂ] sym (b ⊗ₜ[ℂ] c)) ⊗ₜ[ℂ] f=_
  rw [SymmetricCubeHook.multiply_pure]

/-- A covector annihilating a nonzero direction produces an actual
nonzero cubic contraction-kernel vector. -/
theorem exists_kernel_ne_zero (a : A) (f : Module.Dual ℂ A)
    (ha : a≠0) (hf : f≠0) (hfa : f a=0) :
    ∃ x : LinearMap.ker (contract (A := A)), x≠0 := by
  obtain ⟨g,hg⟩ := Module.Projective.exists_dual_eq_one ℂ ha
  let F := SymmetricPowerOperations.powerEval 3 g
  have hF : F (SymmetricPower.tprod ℂ ![a,a,a])=1 := by
    simp [F, SymmetricPowerOperations.powerEval_pure, Fin.prod_univ_succ, hg]
  let x : LinearMap.ker (contract (A := A)) :=
    ⟨SymmetricPower.tprod ℂ ![a,a,a] ⊗ₜ[ℂ] f, by
      rw [LinearMap.mem_ker, contract_pure, hfa, zero_smul, add_zero, add_zero]⟩
  refine ⟨x, ?_⟩
  intro hx
  have ht : SymmetricPower.tprod ℂ ![a,a,a] ⊗ₜ[ℂ] f=0 := congrArg Subtype.val hx
  have hz := congrArg (fun z =>
    (TensorProduct.lid ℂ (Module.Dual ℂ A)) (TensorProduct.map F LinearMap.id z)) ht
  change F (SymmetricPower.tprod ℂ ![a,a,a]) • f=0 at hz
  rw [hF, one_smul] at hz
  exact hf hz

variable [FiniteDimensional ℂ A]

theorem contract_insertPair (p : Pair (A := A)) (a b : A) :
    contract (insertPair (p ⊗ₜ[ℂ] sym (a ⊗ₜ[ℂ] b)))=
      LinearMap.trace ℂ A (SymmetricSquareContraction.pairEnd p) • sym (a ⊗ₜ[ℂ] b)+
      sym ((SymmetricSquareContraction.pairEnd p) a ⊗ₜ[ℂ] b)+
      sym (a ⊗ₜ[ℂ] (SymmetricSquareContraction.pairEnd p) b) := by
  induction p using TensorProduct.inductionOn with
  | add p q hp hq =>
    simp only [TensorProduct.add_tmul, map_add, hp, hq, LinearMap.add_apply,
      add_smul, TensorProduct.add_tmul, TensorProduct.tmul_add]
    module
  | tmul c f =>
    rw [insertPair_pure, contract_pure, SymmetricSquareContraction.pairEnd_pure,
      LinearMap.trace_smulRight]
    simp only [LinearMap.smulRight_apply, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
      map_smul, sym_swap a c]

def sectionMap : Sym[ℂ]^2 A →ₗ[ℂ] Source (A := A) :=
  ((Module.finrank ℂ A : ℂ)+2)⁻¹ • insertPair.comp
    (TensorProduct.mk ℂ _ _ (SymmetricSquareContraction.coevaluation (A := A)))

theorem contract_section (x : Sym[ℂ]^2 A) : contract (sectionMap x)=x := by
  have hn : ((Module.finrank ℂ A : ℂ)+2)≠0 := by
    exact_mod_cast (show Module.finrank ℂ A+2≠0 by omega)
  have h : (contract (A := A)).comp sectionMap=LinearMap.id := by
    apply SymmetricPower.ext
    intro v
    rw [← sym_eta v]
    simp only [LinearMap.comp_apply, sectionMap, LinearMap.smul_apply,
      TensorProduct.mk_apply, map_smul, contract_insertPair,
      SymmetricSquareContraction.coevaluation, LinearEquiv.apply_symm_apply,
      LinearMap.trace_id, LinearMap.id_apply]
    rw [show (Module.finrank ℂ A : ℂ) • sym (v 0 ⊗ₜ[ℂ] v 1)+
        sym (v 0 ⊗ₜ[ℂ] v 1)+sym (v 0 ⊗ₜ[ℂ] v 1)=
        ((Module.finrank ℂ A : ℂ)+2) • sym (v 0 ⊗ₜ[ℂ] v 1) by module,
      smul_smul, inv_mul_cancel₀ hn, one_smul]
  exact LinearMap.congr_fun h x

abbrev Kernel := LinearMap.ker (contract (A := A))

def project : Source (A := A) →ₗ[ℂ] Kernel (A := A) :=
  SectionKernel.project contract sectionMap contract_section

def equivalence : Source (A := A) ≃ₗ[ℂ] (Sym[ℂ]^2 A) × Kernel (A := A) :=
  SectionKernel.equivalence contract sectionMap contract_section

end
end Math.SymmetricCubeContraction
