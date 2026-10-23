import Math.RepresentationTheory.Symmetric.SymmetricTensorTrace
import Math.LinearAlgebra.Symmetric.SymmetricPowerLowDegree
import Math.RepresentationTheory.Symmetric.SymmetricCubeContraction
import Math.RepresentationTheory.Symmetric.SymmetricSquarePartialTrace

/-! The concrete reachable color contraction kernels satisfy the single-slot
trace condition after normalized symmetric embedding. All comparisons are
universal pure-power identities, rather than dimension evaluations. -/
namespace Math.RestrictedColorTraces
set_option autoImplicit false
noncomputable section
open Representation TensorSquareQuotients
open scoped TensorProduct

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  (rho : Representation ℂ G V)

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance (A : Type*) [AddCommGroup A] [Module ℂ A] (n : ℕ) :
    AddCommGroup (Sym[ℂ]^n A) := Module.addCommMonoidToAddCommGroup ℂ

def addDualOne (p : ℕ) : (Sym[ℂ]^p V ⊗[ℂ] Module.Dual ℂ V) →ₗ[ℂ]
    SymmetricTensorTrace.Symmetric (V := V) p 1 :=
  TensorProduct.map LinearMap.id SymmetricPowerLowDegree.inclusion

def removeDualZero (p : ℕ) : SymmetricTensorTrace.Symmetric (V := V) p 0 →ₗ[ℂ] Sym[ℂ]^p V :=
  (TensorProduct.rid ℂ _).toLinearMap.comp
    (TensorProduct.map LinearMap.id SymmetricPowerLowDegree.zeroEvaluation)

def removeDualZeroEquiv (p : ℕ) :
    SymmetricTensorTrace.Symmetric (V := V) p 0 ≃ₗ[ℂ] Sym[ℂ]^p V :=
  (TensorProduct.congr (.refl ℂ _) SymmetricPowerLowDegree.zeroEquiv).trans
    (TensorProduct.rid ℂ _)

def trace21 : SymmetricSquareContraction.Source (A := V) →ₗ[ℂ] V :=
  SymmetricPowerLowDegree.evaluation.comp
    ((removeDualZero 1).comp ((SymmetricTensorTrace.trace rho 1 0).comp (addDualOne 2)))

def trace31 : SymmetricCubeContraction.Source (A := V) →ₗ[ℂ] Sym[ℂ]^2 V :=
  (removeDualZero 2).comp ((SymmetricTensorTrace.trace rho 2 0).comp (addDualOne 3))

def onePair : SymmetricTensorTrace.Symmetric (V := V) 1 1 ≃ₗ[ℂ] (V ⊗[ℂ] Module.Dual ℂ V) :=
  TensorProduct.congr SymmetricPowerLowDegree.oneEquiv SymmetricPowerLowDegree.oneEquiv

def trace22 : SymmetricSquarePartialTrace.Source (A := V) →ₗ[ℂ]
    V ⊗[ℂ] Module.Dual ℂ V :=
  onePair.toLinearMap.comp (SymmetricTensorTrace.trace rho 1 1)

theorem trace21_pure (v : V) (f : Module.Dual ℂ V) :
    trace21 rho (SymmetricPower.tprod ℂ (fun _ : Fin 2 => v) ⊗ₜ[ℂ] f) = f v • v := by
  simp only [trace21,LinearMap.comp_apply,addDualOne,TensorProduct.map_tmul,LinearMap.id_apply,
    SymmetricPowerLowDegree.inclusion_apply]
  rw [SymmetricTensorTrace.trace_pure rho 1 0]
  simp [removeDualZero,SymmetricPowerLowDegree.evaluation_tprod]

theorem trace31_pure (v : V) (f : Module.Dual ℂ V) :
    trace31 rho (SymmetricPower.tprod ℂ (fun _ : Fin 3 => v) ⊗ₜ[ℂ] f) =
      f v • SymmetricPower.tprod ℂ (fun _ : Fin 2 => v) := by
  simp only [trace31,LinearMap.comp_apply,addDualOne,TensorProduct.map_tmul,LinearMap.id_apply,
    SymmetricPowerLowDegree.inclusion_apply]
  rw [SymmetricTensorTrace.trace_pure rho 2 0]
  simp [removeDualZero]

theorem trace22_pure (v : V) (f : Module.Dual ℂ V) :
    trace22 rho (SymmetricPower.tprod ℂ (fun _ : Fin 2 => v) ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ (fun _ : Fin 2 => f)) = f v • (v ⊗ₜ[ℂ] f) := by
  change onePair (SymmetricTensorTrace.trace rho 1 1
    (SymmetricPower.tprod ℂ (fun _ : Fin 2 => v) ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ (fun _ : Fin 2 => f))) = _
  rw [SymmetricTensorTrace.trace_pure rho 1 1]
  simp [onePair,SymmetricPowerLowDegree.oneEquiv]

theorem square_contract : SymmetricSquareContraction.contract (A := V) = (2 : ℂ) • trace21 rho := by
  apply TensorProduct.ext'
  intro x f
  suffices he : (SymmetricSquareContraction.contract (A := V)).comp
      ((TensorProduct.mk ℂ _ _).flip f) =
        ((2 : ℂ) • trace21 rho).comp ((TensorProduct.mk ℂ _ _).flip f) from
    LinearMap.congr_fun he x
  apply SymmetricPurePowers.ext
  intro v
  change SymmetricSquareContraction.contract
      (SymmetricPower.tprod ℂ (fun _ : Fin 2 => v) ⊗ₜ[ℂ] f) =
    (2 : ℂ) • trace21 rho (SymmetricPower.tprod ℂ (fun _ : Fin 2 => v) ⊗ₜ[ℂ] f)
  rw [trace21_pure]
  change SymmetricSquareContraction.contract (sym (v ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] f) = _
  rw [SymmetricSquareContraction.contract_pure]
  module

theorem cube_contract : SymmetricCubeContraction.contract (A := V) = (3 : ℂ) • trace31 rho := by
  apply TensorProduct.ext'
  intro x f
  suffices he : (SymmetricCubeContraction.contract (A := V)).comp
      ((TensorProduct.mk ℂ _ _).flip f) =
        ((3 : ℂ) • trace31 rho).comp ((TensorProduct.mk ℂ _ _).flip f) from
    LinearMap.congr_fun he x
  apply SymmetricPurePowers.ext
  intro v
  change SymmetricCubeContraction.contract
      (SymmetricPower.tprod ℂ (fun _ : Fin 3 => v) ⊗ₜ[ℂ] f) =
    (3 : ℂ) • trace31 rho (SymmetricPower.tprod ℂ (fun _ : Fin 3 => v) ⊗ₜ[ℂ] f)
  rw [trace31_pure]
  change SymmetricCubeContraction.contract (SymmetricPower.tprod ℂ ![v,v,v] ⊗ₜ[ℂ] f) = _
  rw [SymmetricCubeContraction.contract_pure]
  rw [sym_tmul]
  have hv : (![v,v] : Fin 2 → V) = (fun _ : Fin 2 => v) := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  module

theorem square_square_contract : SymmetricSquarePartialTrace.contract (A := V) =
    (4 : ℂ) • trace22 rho := by
  apply SymmetricPurePowers.tensor_ext
  intro v f
  change SymmetricSquarePartialTrace.contract
      (SymmetricPower.tprod ℂ (fun _ : Fin 2 => v) ⊗ₜ[ℂ]
        SymmetricPower.tprod ℂ (fun _ : Fin 2 => f)) =
    (4 : ℂ) • trace22 rho (SymmetricPower.tprod ℂ (fun _ : Fin 2 => v) ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ (fun _ : Fin 2 => f))
  rw [trace22_pure]
  change SymmetricSquarePartialTrace.contract (sym (v ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] sym (f ⊗ₜ[ℂ] f)) = _
  rw [SymmetricSquarePartialTrace.contract_pure]
  module

theorem square_kernel_trace (x : LinearMap.ker (SymmetricSquareContraction.contract (A := V))) :
    trace21 rho x.val = 0 := by
  have he : (2 : ℂ) • trace21 rho x.val = 0 := by
    change ((2 : ℂ) • trace21 rho) x.val = 0
    rw [← square_contract rho]
    exact x.property
  exact (smul_eq_zero.mp he).resolve_left (by norm_num)

theorem cube_kernel_trace (x : LinearMap.ker (SymmetricCubeContraction.contract (A := V))) :
    trace31 rho x.val = 0 := by
  have he : (3 : ℂ) • trace31 rho x.val = 0 := by
    change ((3 : ℂ) • trace31 rho) x.val = 0
    rw [← cube_contract rho]
    exact x.property
  exact (smul_eq_zero.mp he).resolve_left (by norm_num)

theorem square_square_kernel_trace
    (x : LinearMap.ker (SymmetricSquarePartialTrace.contract (A := V))) :
    trace22 rho x.val = 0 := by
  have he : (4 : ℂ) • trace22 rho x.val = 0 := by
    change ((4 : ℂ) • trace22 rho) x.val = 0
    rw [← square_square_contract rho]
    exact x.property
  exact (smul_eq_zero.mp he).resolve_left (by norm_num)

theorem square_kernel_rawTrace
    (x : LinearMap.ker (SymmetricSquareContraction.contract (A := V))) :
    SymmetricTensorTrace.rawTrace 1 0
      (SymmetricTensorTrace.inclusion rho 2 1 (addDualOne 2 x.val)) = 0 := by
  apply (SymmetricTensorTrace.rawTrace_zero_iff rho 1 0 _).mpr
  apply (removeDualZeroEquiv (V := V) 1).injective
  apply SymmetricPowerLowDegree.oneEquiv.injective
  change trace21 rho x.val = 0
  exact square_kernel_trace rho x

theorem cube_kernel_rawTrace
    (x : LinearMap.ker (SymmetricCubeContraction.contract (A := V))) :
    SymmetricTensorTrace.rawTrace 2 0
      (SymmetricTensorTrace.inclusion rho 3 1 (addDualOne 3 x.val)) = 0 := by
  apply (SymmetricTensorTrace.rawTrace_zero_iff rho 2 0 _).mpr
  apply (removeDualZeroEquiv (V := V) 2).injective
  change trace31 rho x.val = 0
  exact cube_kernel_trace rho x

theorem square_square_kernel_rawTrace
    (x : LinearMap.ker (SymmetricSquarePartialTrace.contract (A := V))) :
    SymmetricTensorTrace.rawTrace 1 1 (SymmetricTensorTrace.inclusion rho 2 2 x.val) = 0 := by
  apply (SymmetricTensorTrace.rawTrace_zero_iff rho 1 1 _).mpr
  apply (onePair (V := V)).injective
  change trace22 rho x.val = 0
  exact square_square_kernel_trace rho x

def squareFlag (v : V) (f : Module.Dual ℂ V) (hf : f v = 0) :
    LinearMap.ker (SymmetricSquareContraction.contract (A := V)) :=
  ⟨sym (v ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] f,by
    rw [LinearMap.mem_ker,SymmetricSquareContraction.contract_pure,hf,zero_smul,add_zero]⟩

def cubeFlag (v : V) (f : Module.Dual ℂ V) (hf : f v = 0) :
    LinearMap.ker (SymmetricCubeContraction.contract (A := V)) :=
  ⟨SymmetricPower.tprod ℂ ![v,v,v] ⊗ₜ[ℂ] f,by
    rw [LinearMap.mem_ker,SymmetricCubeContraction.contract_pure,hf,zero_smul,add_zero,add_zero]⟩

def squareSquareFlag (v : V) (f : Module.Dual ℂ V) (hf : f v = 0) :
    LinearMap.ker (SymmetricSquarePartialTrace.contract (A := V)) :=
  ⟨sym (v ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] sym (f ⊗ₜ[ℂ] f),by
    rw [LinearMap.mem_ker,SymmetricSquarePartialTrace.contract_pure,hf,zero_smul,add_zero,add_zero]⟩

end
end Math.RestrictedColorTraces
