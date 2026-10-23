import Math.LinearAlgebra.Exterior.ExteriorFourthShuffle
import Math.LinearAlgebra.Exterior.ExteriorFourthDoublet22
import Math.LinearAlgebra.Symmetric.SymmetricPurePowers

/-! Universal fourth symmetric-power splitting. The second summand is the
actual exterior multiplication kernel, rather than a supplied Young module.
The shuffle identities hold for arbitrary vectors in any complex module. -/
namespace Math.SymmetricFourth22
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open TensorSquareQuotients ExteriorFourthKernels ExteriorFourthShuffle
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {A : Type*} [AddCommGroup A] [Module ℂ A]
abbrev Source := Sym[ℂ]^2 (Sym[ℂ]^2 A)
@[reducible] local instance : AddCommGroup (Source (A := A)) :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (Source22 (A := A)) :=
  Module.addCommMonoidToAddCommGroup ℂ

def pair (a b c d : A) : Source (A := A) :=
  sym (sym (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] sym (c ⊗ₜ[ℂ] d))

theorem pair_swap_left (a b c d : A) : pair b a c d=pair a b c d := by
  simp only [pair, sym_swap a b]
theorem pair_swap_right (a b c d : A) : pair a b d c=pair a b c d := by
  simp only [pair, sym_swap c d]
theorem pair_swap_pairs (a b c d : A) : pair c d a b=pair a b c d :=
  sym_swap _ _

def toSymmetric : Source22 (A := A) →ₗ[ℂ] Source (A := A) :=
  (4 : ℂ)⁻¹ • sym.comp ((TensorProduct.map sym sym).comp
    ((TensorProduct.tensorTensorTensorComm ℂ A A A A).toLinearMap.comp
      ((TensorProduct.map alternatingSection alternatingSection).comp symmetricSection)))

def toExterior : Source (A := A) →ₗ[ℂ] Source22 (A := A) :=
  (4 : ℂ)⁻¹ • sym.comp ((TensorProduct.map wedge wedge).comp
    ((TensorProduct.tensorTensorTensorComm ℂ A A A A).toLinearMap.comp
      ((TensorProduct.map symmetricSection symmetricSection).comp symmetricSection)))

theorem toSymmetric_pure (a b c d : A) :
    toSymmetric (sym (wedge (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] wedge (c ⊗ₜ[ℂ] d)))=
      pair a c b d-pair a d b c := by
  simp only [toSymmetric, LinearMap.smul_apply, LinearMap.comp_apply,
    symmetricSection_pure, alternatingSection_pure, map_add, map_sub,
    TensorProduct.sub_tmul,
    TensorProduct.tmul_sub, TensorProduct.map_tmul,
    TensorProduct.tensorTensorTensorComm_tmul, LinearEquiv.coe_coe]
  change (4 : ℂ)⁻¹ •
    ((pair a c b d-pair b c a d-(pair a d b c-pair b d a c))+
      (pair c a d b-pair d a c b-(pair c b d a-pair d b c a)))=_
  simp only [pair, sym_swap]
  module

theorem toExterior_pure (a b c d : A) :
    toExterior (pair a b c d)=
      sym (wedge (a ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] d))+
      sym (wedge (a ⊗ₜ[ℂ] d) ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] c)) := by
  simp only [toExterior, pair, LinearMap.smul_apply, LinearMap.comp_apply,
    symmetricSection_pure, map_add, TensorProduct.add_tmul, TensorProduct.tmul_add,
    TensorProduct.map_tmul, TensorProduct.tensorTensorTensorComm_tmul, LinearEquiv.coe_coe]
  simp only [ExteriorSquareTensorDescent.wedge_swap a c, ExteriorSquareTensorDescent.wedge_swap a d,
    ExteriorSquareTensorDescent.wedge_swap b c, ExteriorSquareTensorDescent.wedge_swap b d,
    sym_neg_left, sym_neg_right, smul_smul]
  simp only [sym_swap (wedge (a ⊗ₜ[ℂ] c)) (wedge (b ⊗ₜ[ℂ] d)),
    sym_swap (wedge (a ⊗ₜ[ℂ] d)) (wedge (b ⊗ₜ[ℂ] c))]
  module

theorem source_ext {N : Type*} [AddCommGroup N] [Module ℂ N]
    {f g : Source (A := A) →ₗ[ℂ] N}
    (h : ∀ a b c d, f (pair a b c d)=g (pair a b c d)) : f=g := by
  have ht : f.comp sym=g.comp sym := by
    apply TensorProduct.ext'
    intro x y
    have hx : (f.comp sym).comp ((TensorProduct.mk ℂ _ _).flip y)=
        (g.comp sym).comp ((TensorProduct.mk ℂ _ _).flip y) := by
      apply SymmetricPower.ext
      intro v
      have hy : (f.comp sym).comp (TensorProduct.mk ℂ _ _ (SymmetricPower.tprod ℂ v))=
          (g.comp sym).comp (TensorProduct.mk ℂ _ _ (SymmetricPower.tprod ℂ v)) := by
        apply SymmetricPower.ext
        intro w
        change f (sym (SymmetricPower.tprod ℂ v ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w))=
          g (sym (SymmetricPower.tprod ℂ v ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w))
        rw [← sym_eta v, ← sym_eta w]
        exact h (v 0) (v 1) (w 0) (w 1)
      exact LinearMap.congr_fun hy y
    exact LinearMap.congr_fun hx x
  apply SymmetricPower.ext
  intro v
  rw [← sym_eta v]
  exact LinearMap.congr_fun ht (v 0 ⊗ₜ[ℂ] v 1)

def raw : MultilinearMap ℂ (fun _ : Fin 4 => A) (Source (A := A)) :=
  MultilinearMap.mk' (fun v => pair (v 0) (v 1) (v 2) (v 3)+
    pair (v 0) (v 2) (v 1) (v 3)+pair (v 0) (v 3) (v 1) (v 2))
    (by intro v i x y; fin_cases i <;>
      simp [pair, Function.update, TensorProduct.add_tmul, TensorProduct.tmul_add, map_add] <;> module)
    (by intro v i z x; fin_cases i <;>
      simp [pair, Function.update, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
        map_smul, smul_add])

theorem raw_apply (v : Fin 4 → A) : raw v=pair (v 0) (v 1) (v 2) (v 3)+
    pair (v 0) (v 2) (v 1) (v 3)+pair (v 0) (v 3) (v 1) (v 2) := rfl

theorem raw_swap (i j : Fin 4) (v : Fin 4 → A) : raw (v ∘ Equiv.swap i j)=raw v := by
  rw [raw_apply, raw_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [Function.comp_apply, Equiv.swap_apply_def] <;> norm_num
  all_goals simp only [pair, sym_swap (v 0) (v 1), sym_swap (v 0) (v 2),
    sym_swap (v 0) (v 3), sym_swap (v 1) (v 2), sym_swap (v 1) (v 3),
    sym_swap (v 2) (v 3),
    sym_swap (sym (v 0 ⊗ₜ[ℂ] v 1)) (sym (v 2 ⊗ₜ[ℂ] v 3)),
    sym_swap (sym (v 0 ⊗ₜ[ℂ] v 2)) (sym (v 1 ⊗ₜ[ℂ] v 3)),
    sym_swap (sym (v 0 ⊗ₜ[ℂ] v 3)) (sym (v 1 ⊗ₜ[ℂ] v 2))]
  all_goals abel

theorem raw_symmetric (e : Equiv.Perm (Fin 4)) : ∀ v : Fin 4 → A, raw (v ∘ e)=raw v := by
  induction e using Equiv.Perm.swap_induction_on with
  | one => intro v; rfl
  | swap_mul e i j _ ih =>
    intro v
    change raw ((v ∘ Equiv.swap i j) ∘ e)=raw v
    rw [ih, raw_swap]

def coproduct : Sym[ℂ]^4 A →ₗ[ℂ] Source (A := A) :=
  SymmetricPowerDescent.lift 4 ⟨raw, raw_symmetric⟩

theorem coproduct_pure (a b c d : A) :
    coproduct (SymmetricPower.tprod ℂ ![a,b,c,d])=
      pair a b c d+pair a c b d+pair a d b c :=
  SymmetricPowerDescent.lift_tprod _ _ _

def multiply : Source (A := A) →ₗ[ℂ] Sym[ℂ]^4 A :=
  (8 : ℂ)⁻¹ • (TensorFourthMultilinear.fromMultilinear (SymmetricPower.tprod ℂ)).comp
    ((TensorProduct.assoc ℂ A A (A ⊗[ℂ] A)).toLinearMap.comp
      ((TensorProduct.map symmetricSection symmetricSection).comp symmetricSection))

theorem power_swap01 (a b c d : A) :
    SymmetricPower.tprod ℂ ![b,a,c,d]=SymmetricPower.tprod ℂ ![a,b,c,d] := by
  convert SymmetricPower.tprod_equiv (R := ℂ) (Equiv.swap (0 : Fin 4) 1) ![a,b,c,d] using 1
  congr 1
  ext i
  fin_cases i <;> rfl

theorem power_swap23 (a b c d : A) :
    SymmetricPower.tprod ℂ ![a,b,d,c]=SymmetricPower.tprod ℂ ![a,b,c,d] := by
  convert SymmetricPower.tprod_equiv (R := ℂ) (Equiv.swap (2 : Fin 4) 3) ![a,b,c,d] using 1
  congr 1
  ext i
  fin_cases i <;> rfl

theorem power_swap_pairs (a b c d : A) :
    SymmetricPower.tprod ℂ ![c,d,a,b]=SymmetricPower.tprod ℂ ![a,b,c,d] := by
  convert SymmetricPower.tprod_equiv (R := ℂ)
    ((Equiv.swap (0 : Fin 4) 2)*(Equiv.swap 1 3)) ![a,b,c,d] using 1
  congr 1
  ext i
  fin_cases i <;> rfl

theorem multiply_pure (a b c d : A) :
    multiply (pair a b c d)=SymmetricPower.tprod ℂ ![a,b,c,d] := by
  simp only [multiply, pair, LinearMap.smul_apply, LinearMap.comp_apply,
    symmetricSection_pure, map_add, TensorProduct.add_tmul, TensorProduct.tmul_add,
    TensorProduct.map_tmul, LinearEquiv.coe_coe, TensorProduct.assoc_tmul,
    TensorFourthMultilinear.from_pure]
  rw [power_swap01 a b c d, power_swap01 a b d c, power_swap23 a b c d,
    power_swap01 c d a b, power_swap01 c d b a, power_swap23 c d a b,
    power_swap_pairs a b c d]
  module

theorem exterior_symmetric_composite : (toExterior (A := A)).comp toSymmetric=
    (3 : ℂ) • LinearMap.id-delta22.comp multiply22 := by
  apply ExteriorFourthDoublet22.source22_ext
  intro a b c d
  change toExterior (toSymmetric (sym (wedge (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] wedge (c ⊗ₜ[ℂ] d))))=
    (3 : ℂ) • sym (wedge (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] wedge (c ⊗ₜ[ℂ] d))-
      delta22 (multiply22 (sym (wedge (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] wedge (c ⊗ₜ[ℂ] d))))
  rw [toSymmetric_pure, map_sub, toExterior_pure, toExterior_pure,
    multiply22_pure, delta22_pure]
  simp only [ExteriorSquareTensorDescent.wedge_swap b c,
    ExteriorSquareTensorDescent.wedge_swap b d, ExteriorSquareTensorDescent.wedge_swap c d,
    sym_neg_right]
  module

theorem symmetric_exterior_composite : (toSymmetric (A := A)).comp toExterior=
    (3 : ℂ) • LinearMap.id-coproduct.comp multiply := by
  apply source_ext
  intro a b c d
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
  rw [toExterior_pure, map_add, toSymmetric_pure, toSymmetric_pure,
    multiply_pure, coproduct_pure, pair_swap_right a b c d,
    pair_swap_right a c b d, pair_swap_right a d b c]
  module

theorem power_diagonal (a : A) : SymmetricPower.tprod ℂ (fun _ : Fin 4 => a)=
    SymmetricPower.tprod ℂ ![a,a,a,a] := by
  congr 1
  ext i
  fin_cases i <;> rfl

theorem multiply_coproduct (x : Sym[ℂ]^4 A) : multiply (coproduct x)=(3 : ℂ) • x := by
  have h : (multiply (A := A)).comp coproduct=(3 : ℂ) • LinearMap.id := by
    apply SymmetricPurePowers.ext
    intro a
    change multiply (coproduct (SymmetricPower.tprod ℂ (fun _ : Fin 4 => a)))=
      (3 : ℂ) • SymmetricPower.tprod ℂ (fun _ : Fin 4 => a)
    rw [power_diagonal, coproduct_pure, map_add, map_add, multiply_pure]
    module
  exact LinearMap.congr_fun h x

theorem toExterior_coproduct (x : Sym[ℂ]^4 A) : toExterior (coproduct x)=0 := by
  have h : (toExterior (A := A)).comp coproduct=0 := by
    apply SymmetricPurePowers.ext
    intro a
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [power_diagonal, coproduct_pure, map_add, map_add, toExterior_pure]
    simp only [ExteriorCubeHook.wedge_self, TensorProduct.zero_tmul, map_zero, add_zero]
  exact LinearMap.congr_fun h x

theorem multiply22_toExterior (x : Source (A := A)) : multiply22 (toExterior x)=0 := by
  have h : (multiply22 (A := A)).comp toExterior=0 := by
    apply source_ext
    intro a b c d
    change multiply22 (toExterior (pair a b c d))=0
    rw [toExterior_pure, map_add, multiply22_pure, multiply22_pure]
    have h1 : fourth a c b d= -fourth a b c d := by
      have hv : (![a,b,c,d] ∘ Equiv.swap (1 : Fin 4) 2)=![a,c,b,d] := by
        ext i
        fin_cases i <;> rfl
      simpa only [hv, fourth] using (exteriorPower.ιMulti ℂ 4).map_swap ![a,b,c,d]
        (by decide : (1 : Fin 4)≠2)
    have h2 : fourth a d b c= -fourth a b d c := by
      have hv : (![a,b,d,c] ∘ Equiv.swap (1 : Fin 4) 2)=![a,d,b,c] := by
        ext i
        fin_cases i <;> rfl
      simpa only [hv, fourth] using (exteriorPower.ιMulti ℂ 4).map_swap ![a,b,d,c]
        (by decide : (1 : Fin 4)≠2)
    have h3 : fourth a b d c= -fourth a b c d := by
      have hv : (![a,b,c,d] ∘ Equiv.swap (2 : Fin 4) 3)=![a,b,d,c] := by
        ext i
        fin_cases i <;> rfl
      simpa only [hv, fourth] using (exteriorPower.ιMulti ℂ 4).map_swap ![a,b,c,d]
        (by decide : (2 : Fin 4)≠3)
    rw [h1, h2, h3, neg_neg, neg_add_cancel]
  exact LinearMap.congr_fun h x

theorem multiply_toSymmetric (x : Source22 (A := A)) : multiply (toSymmetric x)=0 := by
  have h : (multiply (A := A)).comp toSymmetric=0 := by
    apply ExteriorFourthDoublet22.source22_ext
    intro a b c d
    change multiply (toSymmetric (sym (wedge (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] wedge (c ⊗ₜ[ℂ] d))))=0
    rw [toSymmetric_pure, map_sub, multiply_pure, multiply_pure]
    have hp : SymmetricPower.tprod ℂ ![a,d,b,c]=SymmetricPower.tprod ℂ ![a,c,b,d] := by
      convert SymmetricPower.tprod_equiv (R := ℂ) (Equiv.swap (1 : Fin 4) 3) ![a,c,b,d] using 1
      congr 1
      ext i
      fin_cases i <;> rfl
    rw [hp, sub_self]
  exact LinearMap.congr_fun h x

def toKernel : Source (A := A) →ₗ[ℂ] K22 (A := A) :=
  toExterior.codRestrict _ multiply22_toExterior

/-- Complete universal splitting, with actual inverse shuffle maps. -/
def equivalence : Source (A := A) ≃ₗ[ℂ] (Sym[ℂ]^4 A) × K22 (A := A) where
  toLinearMap := multiply.prod ((3 : ℂ)⁻¹ • toKernel)
  invFun x := (3 : ℂ)⁻¹ • coproduct x.1+toSymmetric x.2.val
  left_inv x := by
    change (3 : ℂ)⁻¹ • coproduct (multiply x)+toSymmetric ((3 : ℂ)⁻¹ • toExterior x)=x
    have h := LinearMap.congr_fun (symmetric_exterior_composite (A := A)) x
    change toSymmetric (toExterior x)=(3 : ℂ) • x-coproduct (multiply x) at h
    rw [map_smul, h, smul_sub, smul_smul]
    norm_num
  right_inv x := by
    apply Prod.ext
    · change multiply ((3 : ℂ)⁻¹ • coproduct x.1+toSymmetric x.2.val)=x.1
      rw [map_add, map_smul, multiply_coproduct, multiply_toSymmetric, add_zero, smul_smul]
      norm_num
    · apply Subtype.ext
      change (3 : ℂ)⁻¹ • toExterior ((3 : ℂ)⁻¹ • coproduct x.1+toSymmetric x.2.val)=x.2.val
      have h := LinearMap.congr_fun (exterior_symmetric_composite (A := A)) x.2.val
      change toExterior (toSymmetric x.2.val)=(3 : ℂ) • x.2.val-
        delta22 (multiply22 x.2.val) at h
      rw [show multiply22 x.2.val=0 from x.2.property, map_zero, sub_zero] at h
      rw [map_add, map_smul, toExterior_coproduct, smul_zero, zero_add, h, smul_smul]
      norm_num

end
end Math.SymmetricFourth22
