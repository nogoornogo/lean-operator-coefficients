import Math.RepresentationTheory.Color.Diagrams.RestrictedColorDuality
import Math.RepresentationTheory.Tensors.TensorPowerEquivalence
import Math.RepresentationTheory.Symmetric.SymmetricTensorTrace

/-! The actual trace-free endomorphism branch is a split raw (1,1) vertex,
with its single contraction zero and exact incident-flag witnesses. -/
namespace Math.TraceFreeColorVertex
set_option autoImplicit false
noncomputable section
open Representation SplitRepresentationProjection ExternalInvariantTensor
open scoped TensorProduct

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (rho : Representation ℂ G V)

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance (A : Type*) [AddCommGroup A] [Module ℂ A] (n : ℕ) :
    AddCommGroup (⨂[ℂ]^n A) := inferInstance

abbrev raw : Representation ℂ G (SymmetricTensorTrace.Raw (V := V) 1 1) :=
  (rho.tensorPower 1).tprod (rho.dual.tensorPower 1)

def whole : Representation.Equiv (raw rho) (TraceEndomorphismSplit.action rho) :=
  (tensorEquiv (TensorPowerEquivalence.one rho) (TensorPowerEquivalence.one rho.dual)).trans
    (TraceFreeCoefficientExclusion.tensorEnd rho)

def split (hd : Module.finrank ℂ V ≠ 0) : Split (raw rho) (TraceEndomorphismSplit.traceFreeAction rho) :=
  ((Split.ofEquiv (whole rho)).trans
    (Split.ofEquiv (TraceEndomorphismSplit.equivalence rho hd).symm)).trans
      (Split.snd (trivial ℂ G ℂ) (TraceEndomorphismSplit.traceFreeAction rho))

theorem embed_end (hd : Module.finrank ℂ V ≠ 0) (x : TraceEndomorphismSplit.TraceFree rho) :
    whole rho ((split rho hd).embed x) = x.val := by
  change whole rho ((whole rho).symm (TraceEndomorphismSplit.equivalence rho hd (0,x))) = x.val
  rw [Representation.Equiv.apply_symm_apply]
  change TraceEndomorphismSplit.scalar rho 0 + x.val = x.val
  rw [map_zero,zero_add]

def emptyScalar : SymmetricTensorTrace.Raw (V := V) 0 0 ≃ₗ[ℂ] ℂ :=
  (TensorProduct.congr
    (PiTensorProduct.isEmptyEquiv (Fin 0) (R := ℂ) (s := fun _ => V))
    (PiTensorProduct.isEmptyEquiv (Fin 0) (R := ℂ) (s := fun _ => Module.Dual ℂ V))).trans
      (TensorProduct.lid ℂ ℂ)

theorem whole_pure (v : V) (f : Module.Dual ℂ V) :
    whole rho (PiTensorProduct.tprod ℂ (fun _ : Fin 1 => v) ⊗ₜ[ℂ]
      PiTensorProduct.tprod ℂ (fun _ : Fin 1 => f)) = f.smulRight v := by
  change TraceFreeCoefficientExclusion.tensorEnd rho
    (TensorProduct.congr (TensorPowerEquivalence.one rho).toLinearEquiv
      (TensorPowerEquivalence.one rho.dual).toLinearEquiv
        (PiTensorProduct.tprod ℂ (fun _ : Fin 1 => v) ⊗ₜ[ℂ]
          PiTensorProduct.tprod ℂ (fun _ : Fin 1 => f))) = _
  rw [TensorProduct.congr_tmul]
  change TraceFreeCoefficientExclusion.tensorEnd rho
    ((PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => V) 0)
        (PiTensorProduct.tprod ℂ (fun _ : Fin 1 => v)) ⊗ₜ[ℂ]
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => Module.Dual ℂ V) 0)
        (PiTensorProduct.tprod ℂ (fun _ : Fin 1 => f))) = _
  rw [PiTensorProduct.subsingletonEquiv_apply_tprod,PiTensorProduct.subsingletonEquiv_apply_tprod]
  rfl

theorem trace_identity (z : SymmetricTensorTrace.Raw (V := V) 1 1) :
    emptyScalar (SymmetricTensorTrace.rawTrace 0 0 z) = LinearMap.trace ℂ V (whole rho z) := by
  suffices he : emptyScalar.toLinearMap.comp (SymmetricTensorTrace.rawTrace (V := V) 0 0) =
      (LinearMap.trace ℂ V).comp (whole rho).toLinearEquiv.toLinearMap from
    LinearMap.congr_fun he z
  apply TensorProduct.ext'
  intro x y
  have hx : x ∈ Submodule.span ℂ (Set.range (PiTensorProduct.tprod ℂ (s := fun _ : Fin 1 => V))) := by
    rw [PiTensorProduct.span_tprod_eq_top]; trivial
  have hy : y ∈ Submodule.span ℂ
      (Set.range (PiTensorProduct.tprod ℂ (s := fun _ : Fin 1 => Module.Dual ℂ V))) := by
    rw [PiTensorProduct.span_tprod_eq_top]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f,rfl⟩ := hy
      have hv : v = fun _ : Fin 1 => v 0 := funext (fun i => congrArg v (Subsingleton.elim i 0))
      have hf : f = fun _ : Fin 1 => f 0 := funext (fun i => congrArg f (Subsingleton.elim i 0))
      rw [hv,hf]
      change emptyScalar (SymmetricTensorTrace.rawTrace 0 0
        (PiTensorProduct.tprod ℂ (fun _ : Fin 1 => v 0) ⊗ₜ[ℂ]
          PiTensorProduct.tprod ℂ (fun _ : Fin 1 => f 0))) = _
      rw [SymmetricTensorTrace.rawTrace_pure]
      change emptyScalar ((f 0) (v 0) •
          (PiTensorProduct.tprod ℂ (fun _ : Fin 0 => v 0) ⊗ₜ[ℂ]
            PiTensorProduct.tprod ℂ (fun _ : Fin 0 => f 0))) =
        LinearMap.trace ℂ V (whole rho
          (PiTensorProduct.tprod ℂ (fun _ : Fin 1 => v 0) ⊗ₜ[ℂ]
            PiTensorProduct.tprod ℂ (fun _ : Fin 1 => f 0)))
      rw [whole_pure,LinearMap.trace_smulRight]
      simp [emptyScalar]
    | zero => simp
    | add y w _ _ hy hw => simpa only [TensorProduct.tmul_add,map_add] using congrArg₂ (·+·) hy hw
    | smul c y _ hy => simpa only [TensorProduct.tmul_smul,map_smul] using congrArg (c • ·) hy
  | zero => simp
  | add x w _ _ hx hw => simpa only [TensorProduct.add_tmul,map_add] using congrArg₂ (·+·) hx hw
  | smul c x _ hx => simpa only [← TensorProduct.smul_tmul',map_smul] using congrArg (c • ·) hx

theorem trace_zero (hd : Module.finrank ℂ V ≠ 0) (x : TraceEndomorphismSplit.TraceFree rho) :
    SymmetricTensorTrace.rawTrace 0 0 ((split rho hd).embed x) = 0 := by
  apply (emptyScalar (V := V)).injective
  rw [trace_identity rho,embed_end,map_zero]
  exact x.property

def flag (v : V) (f : Module.Dual ℂ V) (hf : f v = 0) : TraceEndomorphismSplit.TraceFree rho :=
  ⟨f.smulRight v,by change LinearMap.trace ℂ V (f.smulRight v) = 0; rw [LinearMap.trace_smulRight,hf]⟩

theorem flag_embed (hd : Module.finrank ℂ V ≠ 0) (v : V) (f : Module.Dual ℂ V) (hf : f v = 0) :
    (split rho hd).embed (flag rho v f hf) =
      PiTensorProduct.tprod ℂ (fun _ : Fin 1 => v) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun _ : Fin 1 => f) := by
  apply (whole rho).injective
  change whole rho ((split rho hd).embed (flag rho v f hf)) = whole rho
    (PiTensorProduct.tprod ℂ (fun _ : Fin 1 => v) ⊗ₜ[ℂ]
      PiTensorProduct.tprod ℂ (fun _ : Fin 1 => f))
  rw [embed_end,whole_pure]
  rfl

end
end Math.TraceFreeColorVertex
