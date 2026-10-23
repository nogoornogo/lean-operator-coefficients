import Math.LinearAlgebra.Exterior.ExteriorFourthDoublet

/-! The double-determinant insertion for the actual quartic K22 kernel. -/
namespace Math.ExteriorFourthDoublet22
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open TensorSquareQuotients ExteriorCubeHook ExteriorFourthKernels ExteriorFourthShuffle
open TensorFourthMultilinear ExteriorFourthDoublet
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {A : Type*} [AddCommGroup A] [Module ℂ A]
@[reducible] local instance : AddCommGroup (Source22 (A := A)) :=
  Module.addCommMonoidToAddCommGroup ℂ

def colorContract22 : Tensor (V := A) →ₗ[ℂ] Source22 (A := A) :=
  sym.comp ((TensorProduct.map wedge wedge).comp
    (TensorProduct.assoc ℂ A A (A ⊗[ℂ] A)).symm.toLinearMap)

def spinRaw22 : MultilinearMap ℂ (fun _ : Fin 4 => B) ℂ :=
  MultilinearMap.mk' (fun s => SU2DoubletDuality.epsilon (s 0) (s 2)*
    SU2DoubletDuality.epsilon (s 1) (s 3))
    (by intro s i x y; fin_cases i <;>
      simp [Function.update, SU2DoubletDuality.epsilon_apply] <;> ring)
    (by intro s i z x; fin_cases i <;>
      simp [Function.update, SU2DoubletDuality.epsilon_apply, smul_eq_mul] <;> ring)

def raw22 : Tensor (V := A ⊗[ℂ] B) →ₗ[ℂ] Source22 (A := A) :=
  (TensorProduct.rid ℂ _).toLinearMap.comp
    ((TensorProduct.map colorContract22 (fromMultilinear spinRaw22)).comp
      ExteriorFourthColumn.regroup.toLinearMap)

theorem raw22_pure (a b c d : A) (s t u v : B) :
    raw22 ((a ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] ((b ⊗ₜ[ℂ] t) ⊗ₜ[ℂ]
      ((c ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] (d ⊗ₜ[ℂ] v))))=
      (SU2DoubletDuality.epsilon s u*SU2DoubletDuality.epsilon t v) •
        sym (wedge (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] wedge (c ⊗ₜ[ℂ] d)) := rfl

def contract22 : Total (A := A) →ₗ[ℂ] Source22 (A := A) :=
  exteriorPower.alternatingMapLinearEquiv
    (AlternatingFour.alternating (toMultilinear (raw22 (A := A))))

theorem contract22_fourth (x y z w : A ⊗[ℂ] B) :
    contract22 (fourth x y z w)=AlternatingFour.raw (toMultilinear raw22) ![x,y,z,w] := by
  rw [fourth, contract22, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

def middleSwap : Tensor (V := B) →ₗ[ℂ] Tensor (V := B) :=
  fromMultilinear ((toMultilinear (LinearMap.id : Tensor (V := B) →ₗ[ℂ] _)).domDomCongr
    (Equiv.swap 1 2))

theorem middleSwap_pure (s t u v : B) :
    middleSwap (s ⊗ₜ[ℂ] (t ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] v)))=s ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] (t ⊗ₜ[ℂ] v)) := rfl

def spinVolume22 : Tensor (V := B) :=
  middleSwap ((TensorProduct.assoc ℂ B B (B ⊗[ℂ] B))
    ((e0 ⊗ₜ[ℂ] e1-e1 ⊗ₜ[ℂ] e0) ⊗ₜ[ℂ] (e0 ⊗ₜ[ℂ] e1-e1 ⊗ₜ[ℂ] e0)))

theorem spinVolume22_expand : spinVolume22=
    e0 ⊗ₜ[ℂ] (e0 ⊗ₜ[ℂ] (e1 ⊗ₜ[ℂ] e1))-
    e0 ⊗ₜ[ℂ] (e1 ⊗ₜ[ℂ] (e1 ⊗ₜ[ℂ] e0))-
    e1 ⊗ₜ[ℂ] (e0 ⊗ₜ[ℂ] (e0 ⊗ₜ[ℂ] e1))+
    e1 ⊗ₜ[ℂ] (e1 ⊗ₜ[ℂ] (e0 ⊗ₜ[ℂ] e0)) := by
  simp only [spinVolume22, TensorProduct.sub_tmul, TensorProduct.tmul_sub, map_sub,
    TensorProduct.assoc_tmul, middleSwap_pure]
  abel

def colorInsert22 : Source22 (A := A) →ₗ[ℂ] Tensor (V := A) :=
  (TensorProduct.assoc ℂ A A (A ⊗[ℂ] A)).toLinearMap.comp
    ((TensorProduct.map alternatingSection alternatingSection).comp symmetricSection)

def insert22 : Source22 (A := A) →ₗ[ℂ] Total (A := A) :=
  (fromMultilinear (exteriorPower.ιMulti ℂ 4).toMultilinearMap).comp
    (ExteriorFourthColumn.regroup.symm.toLinearMap.comp
      (((TensorProduct.mk ℂ (Tensor (V := A)) (Tensor (V := B))).flip spinVolume22).comp
        colorInsert22))

def pack22 (a b c d : A) : Total (A := A) :=
  fourth (a ⊗ₜ[ℂ] e0) (b ⊗ₜ[ℂ] e0) (c ⊗ₜ[ℂ] e1) (d ⊗ₜ[ℂ] e1)-
  fourth (a ⊗ₜ[ℂ] e0) (b ⊗ₜ[ℂ] e1) (c ⊗ₜ[ℂ] e1) (d ⊗ₜ[ℂ] e0)-
  fourth (a ⊗ₜ[ℂ] e1) (b ⊗ₜ[ℂ] e0) (c ⊗ₜ[ℂ] e0) (d ⊗ₜ[ℂ] e1)+
  fourth (a ⊗ₜ[ℂ] e1) (b ⊗ₜ[ℂ] e1) (c ⊗ₜ[ℂ] e0) (d ⊗ₜ[ℂ] e0)

theorem insert22_pure (a b c d : A) :
    insert22 (sym (wedge (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] wedge (c ⊗ₜ[ℂ] d)))=
      pack22 a b c d-pack22 b a c d-pack22 a b d c+pack22 b a d c+
      pack22 c d a b-pack22 d c a b-pack22 c d b a+pack22 d c b a := by
  simp only [insert22, colorInsert22, LinearMap.comp_apply, symmetricSection_pure,
    TensorProduct.map_tmul, alternatingSection_pure, TensorProduct.sub_tmul,
    TensorProduct.tmul_sub, map_add, map_sub,
    TensorProduct.assoc_tmul, LinearEquiv.coe_coe, TensorProduct.mk_apply, LinearMap.flip_apply, LinearMap.add_apply, LinearMap.sub_apply,
    spinVolume22_expand, regroup_symm_pure, from_pure]
  unfold pack22 fourth
  module

theorem contract22_pack22 (a b c d : A) : contract22 (pack22 a b c d)=
    (24 : ℂ) • (sym (wedge (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] wedge (c ⊗ₜ[ℂ] d))-
      sym (wedge (a ⊗ₜ[ℂ] d) ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] c))) := by
  simp only [pack22, map_add, map_sub, contract22_fourth,
    AlternatingFour.raw_apply, AlternatingThree.raw_apply, MultilinearMap.curryLeft_apply,
    toMultilinear, MultilinearMap.mk'_apply, Matrix.Fin.cons_vecCons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, raw22_pure]
  norm_num [SU2DoubletDuality.epsilon_apply, e0, e1, -sym_tmul, -ExteriorSquareTensorDescent.wedge_tmul]
  simp only [ExteriorSquareTensorDescent.wedge_swap a b,
    ExteriorSquareTensorDescent.wedge_swap a c, ExteriorSquareTensorDescent.wedge_swap a d,
    ExteriorSquareTensorDescent.wedge_swap b c, ExteriorSquareTensorDescent.wedge_swap b d,
    ExteriorSquareTensorDescent.wedge_swap c d, sym_neg_left, sym_neg_right,
    sym_swap (wedge (a ⊗ₜ[ℂ] b)) (wedge (c ⊗ₜ[ℂ] d)),
    sym_swap (wedge (a ⊗ₜ[ℂ] c)) (wedge (b ⊗ₜ[ℂ] d)),
    sym_swap (wedge (a ⊗ₜ[ℂ] d)) (wedge (b ⊗ₜ[ℂ] c))]
  module

theorem source22_ext {N : Type*} [AddCommGroup N] [Module ℂ N]
    {f g : Source22 (A := A) →ₗ[ℂ] N}
    (h : ∀ a b c d, f (sym (wedge (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] wedge (c ⊗ₜ[ℂ] d)))=
      g (sym (wedge (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] wedge (c ⊗ₜ[ℂ] d)))) : f=g := by
  have ht : f.comp sym=g.comp sym := by
    apply TensorProduct.ext'
    intro x y
    have hx : (f.comp sym).comp ((TensorProduct.mk ℂ _ _).flip y)=
        (g.comp sym).comp ((TensorProduct.mk ℂ _ _).flip y) := by
      apply exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro v
      have hy : (f.comp sym).comp (TensorProduct.mk ℂ _ _ (exteriorPower.ιMulti ℂ 2 v))=
          (g.comp sym).comp (TensorProduct.mk ℂ _ _ (exteriorPower.ιMulti ℂ 2 v)) := by
        apply exteriorPower.linearMap_ext
        apply AlternatingMap.ext
        intro w
        change f (sym (exteriorPower.ιMulti ℂ 2 v ⊗ₜ[ℂ] exteriorPower.ιMulti ℂ 2 w))=
          g (sym (exteriorPower.ιMulti ℂ 2 v ⊗ₜ[ℂ] exteriorPower.ιMulti ℂ 2 w))
        rw [← wedge_eta v, ← wedge_eta w]
        exact h (v 0) (v 1) (w 0) (w 1)
      exact LinearMap.congr_fun hy y
    exact LinearMap.congr_fun hx x
  apply SymmetricPower.ext
  intro v
  rw [← sym_eta v]
  exact LinearMap.congr_fun ht (v 0 ⊗ₜ[ℂ] v 1)

theorem contract22_insert22 : (contract22 (A := A)).comp insert22=
    (288 : ℂ) • LinearMap.id-(96 : ℂ) • delta22.comp multiply22 := by
  apply source22_ext
  intro a b c d
  change contract22 (insert22 (sym (wedge (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] wedge (c ⊗ₜ[ℂ] d))))=_
  rw [insert22_pure]
  simp only [map_add, map_sub, contract22_pack22, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, LinearMap.comp_apply, multiply22_pure, delta22_pure,
    ExteriorSquareTensorDescent.wedge_swap a b, ExteriorSquareTensorDescent.wedge_swap a c,
    ExteriorSquareTensorDescent.wedge_swap a d, ExteriorSquareTensorDescent.wedge_swap b c,
    ExteriorSquareTensorDescent.wedge_swap b d, ExteriorSquareTensorDescent.wedge_swap c d,
    sym_neg_left, sym_neg_right,
    sym_swap (wedge (a ⊗ₜ[ℂ] b)) (wedge (c ⊗ₜ[ℂ] d)),
    sym_swap (wedge (a ⊗ₜ[ℂ] c)) (wedge (b ⊗ₜ[ℂ] d)),
    sym_swap (wedge (a ⊗ₜ[ℂ] d)) (wedge (b ⊗ₜ[ℂ] c))]
  module

def insertK22 : K22 (A := A) →ₗ[ℂ] Total (A := A) :=
  insert22.comp (K22 (A := A)).subtype

def retractK22 : Total (A := A) →ₗ[ℂ] K22 (A := A) :=
  (288 : ℂ)⁻¹ • (project22 (A := A)).comp contract22

theorem retractK22_insertK22 (x : K22 (A := A)) : retractK22 (insertK22 x)=x := by
  have h := LinearMap.congr_fun (contract22_insert22 (A := A)) x.val
  change contract22 (insert22 x.val)=(288 : ℂ) • x.val-(96 : ℂ) • delta22 (multiply22 x.val) at h
  rw [show multiply22 x.val=0 from x.property, map_zero, smul_zero, sub_zero] at h
  change (288 : ℂ)⁻¹ • project22 (contract22 (insert22 x.val))=x
  rw [h, map_smul, project22_kernel, smul_smul]
  norm_num

theorem insertK22_injective : Function.Injective (insertK22 (A := A)) :=
  Function.LeftInverse.injective retractK22_insertK22

end
end Math.ExteriorFourthDoublet22
