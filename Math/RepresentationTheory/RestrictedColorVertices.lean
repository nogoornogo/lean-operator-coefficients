import Math.RepresentationTheory.RestrictedColorTraces

/-! Canonical raw-tensor retractions onto the concrete reachable color
kernels, with source embeddings and single-pair trace exclusions. -/
namespace Math.RestrictedColorVertices
set_option autoImplicit false
noncomputable section
open Representation SplitRepresentationProjection ExternalInvariantTensor
open scoped TensorProduct

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (rho : Representation ℂ G V)

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance (A : Type*) [AddCommGroup A] [Module ℂ A] (n : ℕ) :
    AddCommGroup (Sym[ℂ]^n A) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance (A : Type*) [AddCommGroup A] [Module ℂ A] (n : ℕ) :
    AddCommGroup (⨂[ℂ]^n A) := inferInstance
@[reducible] local instance : AddCommGroup (SymmetricSquareContractionRepresentation.kernel rho) := by
  change AddCommGroup (LinearMap.ker (SymmetricSquareContraction.contract (A := V)))
  infer_instance
@[reducible] local instance : AddCommGroup (SymmetricCubeContractionRepresentation.kernel rho) := by
  change AddCommGroup (LinearMap.ker (SymmetricCubeContraction.contract (A := V)))
  infer_instance
@[reducible] local instance : AddCommGroup (SymmetricSquarePartialTraceRepresentation.kernel rho) := by
  change AddCommGroup (LinearMap.ker (SymmetricSquarePartialTrace.contract (A := V)))
  infer_instance

abbrev raw (p q : ℕ) : Representation ℂ G (SymmetricTensorTrace.Raw (V := V) p q) :=
  (rho.tensorPower p).tprod (rho.dual.tensorPower q)

def symmetricSplit (p q : ℕ) : Split (raw rho p q)
    ((rho.symmetricPower p).tprod (rho.dual.symmetricPower q)) :=
  (SymmetricTensorSplit.split rho p).tensor (SymmetricTensorSplit.split rho.dual q)

def singleSource (p : ℕ) : Split (raw rho p 1) ((rho.symmetricPower p).tprod rho.dual) :=
  (symmetricSplit rho p 1).trans
    (Split.ofEquiv (tensorEquiv (.refl (rho.symmetricPower p))
      (SymmetricPowerLowDegree.representationOneEquiv rho.dual)))

def square : Split (raw rho 2 1) (SymmetricSquareContractionRepresentation.action rho) :=
  ((singleSource rho 2).trans
    (Split.ofEquiv (SymmetricSquareContractionRepresentation.equivalence rho))).trans
      (Split.snd rho (SymmetricSquareContractionRepresentation.action rho))

def cube : Split (raw rho 3 1) (SymmetricCubeContractionRepresentation.action rho) :=
  ((singleSource rho 3).trans
    (Split.ofEquiv (SymmetricCubeContractionRepresentation.equivalence rho))).trans
      (Split.snd (rho.symmetricPower 2) (SymmetricCubeContractionRepresentation.action rho))

def squareSquare : Split (raw rho 2 2) (SymmetricSquarePartialTraceRepresentation.action rho) :=
  ((symmetricSplit rho 2 2).trans
    (Split.ofEquiv (SymmetricSquarePartialTraceRepresentation.equivalence rho))).trans
      (Split.snd (rho.tprod rho.dual) (SymmetricSquarePartialTraceRepresentation.action rho))

theorem square_embed (x : (SymmetricSquareContractionRepresentation.kernel rho).toSubmodule) :
    (square rho).embed x = SymmetricTensorTrace.inclusion rho 2 1
      (RestrictedColorTraces.addDualOne 2 x.val) := by
  change SymmetricTensorTrace.inclusion rho 2 1
    (RestrictedColorTraces.addDualOne 2 (SymmetricSquareContraction.sectionMap 0+x.val)) = _
  rw [map_zero,zero_add]

theorem cube_embed (x : (SymmetricCubeContractionRepresentation.kernel rho).toSubmodule) :
    (cube rho).embed x = SymmetricTensorTrace.inclusion rho 3 1
      (RestrictedColorTraces.addDualOne 3 x.val) := by
  change SymmetricTensorTrace.inclusion rho 3 1
    (RestrictedColorTraces.addDualOne 3 (SymmetricCubeContraction.sectionMap 0+x.val)) = _
  rw [map_zero,zero_add]

theorem squareSquare_embed (x : (SymmetricSquarePartialTraceRepresentation.kernel rho).toSubmodule) :
    (squareSquare rho).embed x = SymmetricTensorTrace.inclusion rho 2 2 x.val := by
  change SymmetricTensorTrace.inclusion rho 2 2
    (SymmetricSquarePartialTrace.sectionMap 0+x.val) = _
  rw [map_zero,zero_add]

theorem square_trace_zero (x : (SymmetricSquareContractionRepresentation.kernel rho).toSubmodule) :
    SymmetricTensorTrace.rawTrace 1 0 ((square rho).embed x) = 0 := by
  rw [square_embed]
  exact RestrictedColorTraces.square_kernel_rawTrace rho x

theorem cube_trace_zero (x : (SymmetricCubeContractionRepresentation.kernel rho).toSubmodule) :
    SymmetricTensorTrace.rawTrace 2 0 ((cube rho).embed x) = 0 := by
  rw [cube_embed]
  exact RestrictedColorTraces.cube_kernel_rawTrace rho x

theorem squareSquare_trace_zero (x : (SymmetricSquarePartialTraceRepresentation.kernel rho).toSubmodule) :
    SymmetricTensorTrace.rawTrace 1 1 ((squareSquare rho).embed x) = 0 := by
  rw [squareSquare_embed]
  exact RestrictedColorTraces.square_square_kernel_rawTrace rho x

omit [FiniteDimensional ℂ V] in
theorem symmetric_pure (p q : ℕ) (v : V) (f : Module.Dual ℂ V) :
    SymmetricTensorTrace.inclusion rho p q
      (SymmetricPower.tprod ℂ (fun _ : Fin p => v) ⊗ₜ[ℂ]
        SymmetricPower.tprod ℂ (fun _ : Fin q => f)) =
      PiTensorProduct.tprod ℂ (fun _ : Fin p => v) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun _ : Fin q => f) := by
  simp only [SymmetricTensorTrace.inclusion,TensorProduct.map_tmul,
    IntertwiningMap.toLinearMap_apply,SymmetricTensorSplit.section_pure_power]

def squareFlag (v : V) (f : Module.Dual ℂ V) (hf : f v = 0) :
    (SymmetricSquareContractionRepresentation.kernel rho).toSubmodule :=
  ⟨(RestrictedColorTraces.squareFlag v f hf).val, (RestrictedColorTraces.squareFlag v f hf).property⟩

def cubeFlag (v : V) (f : Module.Dual ℂ V) (hf : f v = 0) :
    (SymmetricCubeContractionRepresentation.kernel rho).toSubmodule :=
  ⟨(RestrictedColorTraces.cubeFlag v f hf).val, (RestrictedColorTraces.cubeFlag v f hf).property⟩

def squareSquareFlag (v : V) (f : Module.Dual ℂ V) (hf : f v = 0) :
    (SymmetricSquarePartialTraceRepresentation.kernel rho).toSubmodule :=
  ⟨(RestrictedColorTraces.squareSquareFlag v f hf).val, (RestrictedColorTraces.squareSquareFlag v f hf).property⟩

theorem square_flag_embed (v : V) (f : Module.Dual ℂ V) (hf : f v = 0) :
    (square rho).embed (squareFlag rho v f hf) =
      PiTensorProduct.tprod ℂ (fun _ : Fin 2 => v) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun _ : Fin 1 => f) := by
  rw [square_embed]
  change SymmetricTensorTrace.inclusion rho 2 1
    (RestrictedColorTraces.addDualOne 2 (TensorSquareQuotients.sym (v ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] f)) = _
  rw [TensorSquareQuotients.sym_eta (fun _ : Fin 2 => v)]
  exact symmetric_pure rho 2 1 v f

theorem cube_flag_embed (v : V) (f : Module.Dual ℂ V) (hf : f v = 0) :
    (cube rho).embed (cubeFlag rho v f hf) =
      PiTensorProduct.tprod ℂ (fun _ : Fin 3 => v) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun _ : Fin 1 => f) := by
  rw [cube_embed]
  change SymmetricTensorTrace.inclusion rho 3 1
    (RestrictedColorTraces.addDualOne 3 (SymmetricPower.tprod ℂ ![v,v,v] ⊗ₜ[ℂ] f)) = _
  have hv : (![v,v,v] : Fin 3 → V) = (fun _ : Fin 3 => v) := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  exact symmetric_pure rho 3 1 v f

theorem squareSquare_flag_embed (v : V) (f : Module.Dual ℂ V) (hf : f v = 0) :
    (squareSquare rho).embed (squareSquareFlag rho v f hf) =
      PiTensorProduct.tprod ℂ (fun _ : Fin 2 => v) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun _ : Fin 2 => f) := by
  rw [squareSquare_embed]
  change SymmetricTensorTrace.inclusion rho 2 2
    (TensorSquareQuotients.sym (v ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] TensorSquareQuotients.sym (f ⊗ₜ[ℂ] f)) = _
  rw [TensorSquareQuotients.sym_eta (fun _ : Fin 2 => v),
    TensorSquareQuotients.sym_eta (fun _ : Fin 2 => f)]
  exact symmetric_pure rho 2 2 v f

end
end Math.RestrictedColorVertices
