import Math.RepresentationTheory.Symmetric.SymmetricTensorSplit

/-! A single raw vector/covector contraction on a symmetric vertex agrees
with its induced symmetric trace. The comparison is proved on pure powers,
whose span is proved by polarization. -/
namespace Math.SymmetricTensorTrace
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  (rho : Representation ℂ G V)

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance (A : Type*) [AddCommGroup A] [Module ℂ A] (n : ℕ) :
    AddCommGroup (⨂[ℂ]^n A) := inferInstance
@[reducible] local instance (A : Type*) [AddCommGroup A] [Module ℂ A] (n : ℕ) :
    AddCommGroup (Sym[ℂ]^n A) := Module.addCommMonoidToAddCommGroup ℂ

def first {A : Type*} [AddCommGroup A] [Module ℂ A] (p : ℕ) :
    (⨂[ℂ]^(1+p) A) ≃ₗ[ℂ] A ⊗[ℂ] (⨂[ℂ]^p A) :=
  (_root_.TensorPower.mulEquiv :
    ((⨂[ℂ]^1 A) ⊗[ℂ] (⨂[ℂ]^p A)) ≃ₗ[ℂ] (⨂[ℂ]^(1+p) A)).symm.trans
      (TensorProduct.congr
        (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => A) 0)
        (.refl ℂ _))

theorem first_pure_power {A : Type*} [AddCommGroup A] [Module ℂ A] (p : ℕ) (v : A) :
    first p (PiTensorProduct.tprod ℂ (fun _ : Fin (1+p) => v)) =
      v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun _ : Fin p => v) := by
  have he : (_root_.TensorPower.mulEquiv :
      ((⨂[ℂ]^1 A) ⊗[ℂ] (⨂[ℂ]^p A)) ≃ₗ[ℂ] (⨂[ℂ]^(1+p) A))
        (PiTensorProduct.tprod ℂ (fun _ : Fin 1 => v) ⊗ₜ[ℂ]
          PiTensorProduct.tprod ℂ (fun _ : Fin p => v)) =
      PiTensorProduct.tprod ℂ (fun _ : Fin (1+p) => v) := by
    rw [← _root_.TensorPower.gMul_def,_root_.TensorPower.tprod_mul_tprod]
    congr 1
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [Fin.append]
  rw [← he]
  simp [first]

theorem first_tprod {A : Type*} [AddCommGroup A] [Module ℂ A] (p : ℕ)
    (v : Fin (1+p) → A) :
    first p (PiTensorProduct.tprod ℂ v) = v (Fin.castAdd p 0) ⊗ₜ[ℂ]
      PiTensorProduct.tprod ℂ (fun i => v (Fin.natAdd 1 i)) := by
  have he : (_root_.TensorPower.mulEquiv :
      ((⨂[ℂ]^1 A) ⊗[ℂ] (⨂[ℂ]^p A)) ≃ₗ[ℂ] (⨂[ℂ]^(1+p) A))
        (PiTensorProduct.tprod ℂ (fun i => v (Fin.castAdd p i)) ⊗ₜ[ℂ]
          PiTensorProduct.tprod ℂ (fun i => v (Fin.natAdd 1 i))) =
      PiTensorProduct.tprod ℂ v := by
    rw [← _root_.TensorPower.gMul_def,_root_.TensorPower.tprod_mul_tprod]
    congr 1
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [Fin.append]
  rw [← he]
  simp [first]

abbrev Raw (p q : ℕ) := (⨂[ℂ]^p V) ⊗[ℂ] (⨂[ℂ]^q (Module.Dual ℂ V))
abbrev Symmetric (p q : ℕ) := (Sym[ℂ]^p V) ⊗[ℂ] (Sym[ℂ]^q (Module.Dual ℂ V))
@[reducible] local instance (p q : ℕ) : AddCommGroup (Raw (V := V) p q) := inferInstance
@[reducible] local instance (p q : ℕ) : AddCommGroup (Symmetric (V := V) p q) := inferInstance

def rawTrace (p q : ℕ) : Raw (V := V) (1+p) (1+q) →ₗ[ℂ] Raw (V := V) p q :=
  (TensorProduct.lid ℂ _).toLinearMap.comp
    ((TensorProduct.map (contractRight ℂ V) LinearMap.id).comp
      ((TensorProduct.tensorTensorTensorComm ℂ V (⨂[ℂ]^p V)
        (Module.Dual ℂ V) (⨂[ℂ]^q (Module.Dual ℂ V))).toLinearMap.comp
          (TensorProduct.map (first p).toLinearMap (first q).toLinearMap)))

theorem rawTrace_tprod (p q : ℕ) (v : Fin (1+p) → V)
    (f : Fin (1+q) → Module.Dual ℂ V) :
    rawTrace p q (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ f) =
      f (Fin.castAdd q 0) (v (Fin.castAdd p 0)) •
        (PiTensorProduct.tprod ℂ (fun i => v (Fin.natAdd 1 i)) ⊗ₜ[ℂ]
          PiTensorProduct.tprod ℂ (fun i => f (Fin.natAdd 1 i))) := by
  simp only [rawTrace,LinearMap.comp_apply,TensorProduct.map_tmul,LinearEquiv.coe_coe,
    first_tprod]
  rfl

theorem rawTrace_pure (p q : ℕ) (v : V) (f : Module.Dual ℂ V) :
    rawTrace p q
      (PiTensorProduct.tprod ℂ (fun _ : Fin (1+p) => v) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun _ : Fin (1+q) => f)) =
      f v • (PiTensorProduct.tprod ℂ (fun _ : Fin p => v) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun _ : Fin q => f)) := by
  simp only [rawTrace,LinearMap.comp_apply,TensorProduct.map_tmul,LinearEquiv.coe_coe,
    first_pure_power]
  rfl

def inclusion (p q : ℕ) : Symmetric (V := V) p q →ₗ[ℂ] Raw (V := V) p q :=
  TensorProduct.map (SymmetricTensorSplit.sectionMap rho p).toLinearMap
    (SymmetricTensorSplit.sectionMap rho.dual q).toLinearMap

def projection (p q : ℕ) : Raw (V := V) p q →ₗ[ℂ] Symmetric (V := V) p q :=
  TensorProduct.map (SymmetricTensorSplit.projection rho p).toLinearMap
    (SymmetricTensorSplit.projection rho.dual q).toLinearMap

theorem projection_inclusion (p q : ℕ) (x : Symmetric (V := V) p q) :
    projection rho p q (inclusion rho p q x) = x :=
  ((SymmetricTensorSplit.split rho p).tensor (SymmetricTensorSplit.split rho.dual q)).left_inv x

def reindexLeft (p q : ℕ) (sigma : Equiv.Perm (Fin p)) : Module.End ℂ (Raw (V := V) p q) :=
  TensorProduct.map (PiTensorProduct.reindexRepresentation ℂ V (Fin p) sigma) LinearMap.id

def reindexRight (p q : ℕ) (sigma : Equiv.Perm (Fin q)) : Module.End ℂ (Raw (V := V) p q) :=
  TensorProduct.map LinearMap.id (PiTensorProduct.reindexRepresentation ℂ (Module.Dual ℂ V) (Fin q) sigma)

theorem inclusion_reindexLeft (p q : ℕ) (sigma : Equiv.Perm (Fin p)) (x : Symmetric (V := V) p q) :
    reindexLeft p q sigma (inclusion rho p q x) = inclusion rho p q x := by
  suffices he : (reindexLeft (V := V) p q sigma).comp (inclusion rho p q) = inclusion rho p q from
    LinearMap.congr_fun he x
  apply SymmetricPurePowers.tensor_ext
  intro v f
  simp only [LinearMap.comp_apply,inclusion,TensorProduct.map_tmul,
    IntertwiningMap.toLinearMap_apply,SymmetricTensorSplit.section_pure_power,
    reindexLeft,TensorProduct.map_tmul,LinearMap.id_apply,
    PiTensorProduct.reindexRepresentation_apply,LinearEquiv.coe_coe,PiTensorProduct.reindex_tprod]

theorem inclusion_reindexRight (p q : ℕ) (sigma : Equiv.Perm (Fin q)) (x : Symmetric (V := V) p q) :
    reindexRight p q sigma (inclusion rho p q x) = inclusion rho p q x := by
  suffices he : (reindexRight (V := V) p q sigma).comp (inclusion rho p q) = inclusion rho p q from
    LinearMap.congr_fun he x
  apply SymmetricPurePowers.tensor_ext
  intro v f
  simp only [LinearMap.comp_apply,inclusion,TensorProduct.map_tmul,
    IntertwiningMap.toLinearMap_apply,SymmetricTensorSplit.section_pure_power,
    reindexRight,TensorProduct.map_tmul,LinearMap.id_apply,
    PiTensorProduct.reindexRepresentation_apply,LinearEquiv.coe_coe,PiTensorProduct.reindex_tprod]

def trace (p q : ℕ) : Symmetric (V := V) (1+p) (1+q) →ₗ[ℂ] Symmetric (V := V) p q :=
  (projection rho p q).comp ((rawTrace p q).comp (inclusion rho (1+p) (1+q)))

theorem trace_pure (p q : ℕ) (v : V) (f : Module.Dual ℂ V) :
    trace rho p q (SymmetricPower.tprod ℂ (fun _ : Fin (1+p) => v) ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ (fun _ : Fin (1+q) => f)) =
      f v • (SymmetricPower.tprod ℂ (fun _ : Fin p => v) ⊗ₜ[ℂ]
        SymmetricPower.tprod ℂ (fun _ : Fin q => f)) := by
  simp only [trace,LinearMap.comp_apply,inclusion,TensorProduct.map_tmul,
    IntertwiningMap.toLinearMap_apply,SymmetricTensorSplit.section_pure_power,rawTrace_pure,
    map_smul,projection]
  rfl

theorem trace_inclusion (p q : ℕ) :
    (rawTrace p q).comp (inclusion rho (1+p) (1+q)) =
      (inclusion rho p q).comp (trace rho p q) := by
  apply SymmetricPurePowers.tensor_ext
  intro v f
  simp only [LinearMap.comp_apply,inclusion,TensorProduct.map_tmul,
    IntertwiningMap.toLinearMap_apply,SymmetricTensorSplit.section_pure_power,
    trace_pure,rawTrace_pure,map_smul]

theorem rawTrace_zero_iff (p q : ℕ) (x : Symmetric (V := V) (1+p) (1+q)) :
    rawTrace p q (inclusion rho (1+p) (1+q) x) = 0 ↔ trace rho p q x = 0 := by
  have hi : Function.Injective (inclusion rho p q) :=
    Function.LeftInverse.injective
      ((SymmetricTensorSplit.split rho p).tensor (SymmetricTensorSplit.split rho.dual q)).left_inv
  have he := LinearMap.congr_fun (trace_inclusion rho p q) x
  change rawTrace p q (inclusion rho (1+p) (1+q) x) = inclusion rho p q (trace rho p q x) at he
  rw [he,← map_zero (inclusion rho p q),hi.eq_iff]

end
end Math.SymmetricTensorTrace
