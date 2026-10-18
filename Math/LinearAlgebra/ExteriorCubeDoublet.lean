import Math.LinearAlgebra.ExteriorCubeHook
import Math.LinearAlgebra.AlternatingThree
import Math.LinearAlgebra.TensorCubeMultilinear
import Math.RepresentationTheory.SU2DoubletDuality
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! Universal cubic contraction and insertion for a color space tensor a
spin doublet. The identities are vector identities, with no coefficient or
rank tables. -/
namespace Math.ExteriorCubeDoublet
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open TensorSquareQuotients ExteriorCubeHook

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
variable {A : Type*} [AddCommGroup A] [Module ℂ A]
abbrev B := WeakDoubletScalars.Doublet
abbrev Triple (V : Type*) [AddCommGroup V] [Module ℂ V] := V ⊗[ℂ] (V ⊗[ℂ] V)
abbrev Target := Source (V := A) ⊗[ℂ] B
@[reducible] local instance : AddCommGroup (Target (A := A)) := inferInstance

def regroup : Triple (A ⊗[ℂ] B) ≃ₗ[ℂ] Triple A ⊗[ℂ] Triple B :=
  (TensorProduct.congr (.refl ℂ (A ⊗[ℂ] B)) (TensorProduct.tensorTensorTensorComm ℂ A B A B)).trans
    (TensorProduct.tensorTensorTensorComm ℂ A B (A ⊗[ℂ] A) (B ⊗[ℂ] B))

@[simp] theorem regroup_symm_pure (a b c : A) (s t u : B) :
    (regroup (A := A)).symm ((a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] c)) ⊗ₜ[ℂ] (s ⊗ₜ[ℂ] (t ⊗ₜ[ℂ] u)))=
      (a ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] ((b ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] u)) := rfl

def colorContract : Triple A →ₗ[ℂ] Source (V := A) := TensorProduct.map LinearMap.id wedge

def spinContract : Triple B →ₗ[ℂ] B :=
  (TensorProduct.lid ℂ B).toLinearMap.comp
    ((TensorProduct.map (TensorProduct.lift SU2DoubletDuality.epsilon) LinearMap.id).comp
      (TensorProduct.assoc ℂ B B B).symm.toLinearMap)

def raw : Triple (A ⊗[ℂ] B) →ₗ[ℂ] Target (A := A) :=
  (TensorProduct.map colorContract spinContract).comp regroup.toLinearMap

@[simp] theorem raw_pure (a b c : A) (s t u : B) :
    raw ((a ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] ((b ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] u)))=
      SU2DoubletDuality.epsilon s t • ((a ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] c)) ⊗ₜ[ℂ] u) := by
  change (a ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] c)) ⊗ₜ[ℂ] (SU2DoubletDuality.epsilon s t • u)=_
  rw [TensorProduct.tmul_smul]

def contract : (⋀[ℂ]^3 (A ⊗[ℂ] B)) →ₗ[ℂ] Target (A := A) :=
  exteriorPower.alternatingMapLinearEquiv
    (AlternatingThree.alternating (TensorCubeMultilinear.toMultilinear raw))

theorem contract_cube (x y z : A ⊗[ℂ] B) : contract (cube x y z)=
    raw (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] z))-raw (y ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] z))-
    raw (z ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] x))-raw (x ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] y))+
    raw (y ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] x))+raw (z ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] y)) := by
  rw [cube,contract,exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact AlternatingThree.raw_apply _ _

def e0 : B := Pi.single 0 1
def e1 : B := Pi.single 1 1

def spinInsert : B →ₗ[ℂ] Triple B :=
  (TensorProduct.assoc ℂ B B B).toLinearMap.comp
    (TensorProduct.mk ℂ (B ⊗[ℂ] B) B (e0 ⊗ₜ[ℂ] e1-e1 ⊗ₜ[ℂ] e0))

def insert : Target (A := A) →ₗ[ℂ] ⋀[ℂ]^3 (A ⊗[ℂ] B) :=
  (TensorCubeMultilinear.fromMultilinear (exteriorPower.ιMulti ℂ 3).toMultilinearMap).comp
    (regroup.symm.toLinearMap.comp
      (TensorProduct.map (TensorProduct.map LinearMap.id alternatingSection) spinInsert))

theorem insert_pure (a b c : A) (s : B) :
    insert ((a ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] c)) ⊗ₜ[ℂ] s)=
    cube (a ⊗ₜ[ℂ] e0) (b ⊗ₜ[ℂ] e1) (c ⊗ₜ[ℂ] s)-
    cube (a ⊗ₜ[ℂ] e1) (b ⊗ₜ[ℂ] e0) (c ⊗ₜ[ℂ] s)-
    cube (a ⊗ₜ[ℂ] e0) (c ⊗ₜ[ℂ] e1) (b ⊗ₜ[ℂ] s)+
    cube (a ⊗ₜ[ℂ] e1) (c ⊗ₜ[ℂ] e0) (b ⊗ₜ[ℂ] s) := by
  simp only [insert,LinearMap.comp_apply,TensorProduct.map_tmul,alternatingSection_pure,
    spinInsert,TensorProduct.mk_apply,TensorProduct.sub_tmul,map_sub,
    TensorProduct.assoc_tmul,LinearEquiv.coe_coe,TensorProduct.tmul_sub]
  simp only [LinearMap.id_coe,id_eq,regroup_symm_pure,TensorCubeMultilinear.from_pure]
  change cube (a ⊗ₜ[ℂ] e0) (b ⊗ₜ[ℂ] e1) (c ⊗ₜ[ℂ] s)-
    cube (a ⊗ₜ[ℂ] e0) (c ⊗ₜ[ℂ] e1) (b ⊗ₜ[ℂ] s)-
    (cube (a ⊗ₜ[ℂ] e1) (b ⊗ₜ[ℂ] e0) (c ⊗ₜ[ℂ] s)-
      cube (a ⊗ₜ[ℂ] e1) (c ⊗ₜ[ℂ] e0) (b ⊗ₜ[ℂ] s))=_
  abel

/-- The scalar nine is the universal normalization of these two maps,
not an evaluated representation multiplicity. -/
theorem contract_insert_basis (a b c : A) (i : Fin 2) :
    contract (insert ((a ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] c)) ⊗ₜ[ℂ] Pi.single i 1))=
    (9 : ℂ) • ((a ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] c)) ⊗ₜ[ℂ] Pi.single i 1)-
    (3 : ℂ) • (coproduct (cube a b c) ⊗ₜ[ℂ] Pi.single i 1) := by
  fin_cases i <;> rw [insert_pure]
  all_goals simp only [map_add,map_sub,contract_cube,raw_pure,coproduct_pure]
  all_goals simp [SU2DoubletDuality.epsilon_apply,e0,e1,
    ExteriorSquareTensorDescent.wedge_swap a b,ExteriorSquareTensorDescent.wedge_swap a c,
    ExteriorSquareTensorDescent.wedge_swap b c,TensorProduct.neg_tmul,
    TensorProduct.tmul_neg,TensorProduct.add_tmul,TensorProduct.sub_tmul]
  all_goals module

theorem spin_decompose (s : B) : s=s 0 • e0+s 1 • e1 := by
  ext i
  fin_cases i <;> simp [e0,e1]

theorem contract_insert_pure (a b c : A) (s : B) :
    contract (insert ((a ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] c)) ⊗ₜ[ℂ] s))=
    (9 : ℂ) • ((a ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] c)) ⊗ₜ[ℂ] s)-
    (3 : ℂ) • (coproduct (cube a b c) ⊗ₜ[ℂ] s) := by
  rw [spin_decompose s]
  simp only [TensorProduct.tmul_add,TensorProduct.tmul_smul,map_add,map_smul]
  rw [show e0=Pi.single (0 : Fin 2) 1 from rfl,show e1=Pi.single (1 : Fin 2) 1 from rfl,
    contract_insert_basis,contract_insert_basis]
  module

/-- Test a map on decomposable color wedges and arbitrary spin vectors. -/
theorem source_ext {N : Type*} [AddCommGroup N] [Module ℂ N]
    {f g : Target (A := A) →ₗ[ℂ] N}
    (h : ∀ a b c s, f ((a ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] c)) ⊗ₜ[ℂ] s)=
      g ((a ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] c)) ⊗ₜ[ℂ] s)) : f=g := by
  apply TensorProduct.ext'
  intro x s
  have hs : f.comp ((TensorProduct.mk ℂ (Source (V := A)) B).flip s)=
      g.comp ((TensorProduct.mk ℂ (Source (V := A)) B).flip s) := by
    apply TensorProduct.ext'
    intro a y
    have ha : (f.comp ((TensorProduct.mk ℂ (Source (V := A)) B).flip s)).comp
        (TensorProduct.mk ℂ A (⋀[ℂ]^2 A) a)=
        (g.comp ((TensorProduct.mk ℂ (Source (V := A)) B).flip s)).comp
        (TensorProduct.mk ℂ A (⋀[ℂ]^2 A) a) := by
      apply exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro v
      change f ((a ⊗ₜ[ℂ] exteriorPower.ιMulti ℂ 2 v) ⊗ₜ[ℂ] s)=
        g ((a ⊗ₜ[ℂ] exteriorPower.ιMulti ℂ 2 v) ⊗ₜ[ℂ] s)
      rw [← wedge_eta v]
      exact h a (v 0) (v 1) s
    exact LinearMap.congr_fun ha y
  exact LinearMap.congr_fun hs x

/-- Complete vector identity: contraction after insertion is nine times
the color-hook projection, tensored with the spin identity. -/
theorem contract_insert : (contract (A := A)).comp insert =
    (9 : ℂ) • TensorProduct.map ((Hook (V := A)).subtype.comp project) LinearMap.id := by
  apply source_ext
  intro a b c s
  change contract (insert _)=_
  rw [contract_insert_pure]
  change _=(9 : ℂ) • ((a ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] c)-
    (3 : ℂ)⁻¹ • coproduct (multiply (a ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] c)))) ⊗ₜ[ℂ] s)
  rw [multiply_pure,TensorProduct.sub_tmul,TensorProduct.smul_tmul,TensorProduct.tmul_smul,smul_sub,smul_smul]
  norm_num

/-- The hook component has an actual split embedding into the exterior cube. -/
def hookInsert : (Hook (V := A) ⊗[ℂ] B) →ₗ[ℂ] ⋀[ℂ]^3 (A ⊗[ℂ] B) :=
  insert.comp (TensorProduct.map (Hook (V := A)).subtype LinearMap.id)

def hookRetract : (⋀[ℂ]^3 (A ⊗[ℂ] B)) →ₗ[ℂ] Hook (V := A) ⊗[ℂ] B :=
  (9 : ℂ)⁻¹ • (TensorProduct.map project LinearMap.id).comp contract

theorem hook_retract_insert (x : Hook (V := A) ⊗[ℂ] B) : hookRetract (hookInsert x)=x := by
  have h : (hookRetract (A := A)).comp hookInsert=LinearMap.id := by
    apply TensorProduct.ext'
    intro x s
    have hh := LinearMap.congr_fun (contract_insert (A := A)) (x.val ⊗ₜ[ℂ] s)
    change contract (insert (x.val ⊗ₜ[ℂ] s))=
      (9 : ℂ) • ((project x.val).val ⊗ₜ[ℂ] s) at hh
    change (9 : ℂ)⁻¹ • TensorProduct.map project LinearMap.id
      (contract (insert (x.val ⊗ₜ[ℂ] s)))=x ⊗ₜ[ℂ] s
    rw [hh,project_hook,map_smul,TensorProduct.map_tmul,project_hook,LinearMap.id_apply,
      smul_smul]
    norm_num
  exact LinearMap.congr_fun h x

theorem hookInsert_injective : Function.Injective (hookInsert (A := A)) :=
  Function.HasLeftInverse.injective ⟨hookRetract,hook_retract_insert⟩

end
end Math.ExteriorCubeDoublet
