import Math.LinearAlgebra.ExteriorFourthDoublet22

/-! Cross contractions and the top-column exclusions for quartic doublets. -/
namespace Math.ExteriorFourthDoubletCross
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open TensorSquareQuotients ExteriorCubeHook ExteriorFourthKernels ExteriorFourthShuffle
open TensorFourthMultilinear ExteriorFourthDoublet ExteriorFourthDoublet22
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {A : Type*} [AddCommGroup A] [Module ℂ A]
@[reducible] local instance : AddCommGroup (Source22 (A := A)) :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (Target13 (A := A)) := inferInstance

theorem contract13_pack22 (a b c d : A) : contract13 (pack22 a b c d)=0 := by
  simp only [pack22, map_add, map_sub, contract13_fourth,
    AlternatingFour.raw_apply, AlternatingThree.raw_apply, MultilinearMap.curryLeft_apply,
    toMultilinear, MultilinearMap.mk'_apply, Matrix.Fin.cons_vecCons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, raw13_pure]
  norm_num [SU2DoubletDuality.epsilon_apply, e0, e1, -sym_tmul]
  simp only [cube_swap01 b c d,
    cube_swap12 b c d,
    cube_reverse b c d,
    cube_rotate b c d,
    cube_cycle b c d,
    cube_swap01 a c d,
    cube_swap12 a c d,
    cube_reverse a c d,
    cube_rotate a c d,
    cube_cycle a c d,
    cube_swap01 a b d,
    cube_swap12 a b d,
    cube_reverse a b d,
    cube_rotate a b d,
    cube_cycle a b d,
    cube_swap01 a b c,
    cube_swap12 a b c,
    cube_reverse a b c,
    cube_rotate a b c,
    cube_cycle a b c, tmul_neg_scalar,
    TensorProduct.smul_tmul, TensorProduct.tmul_smul,
    sym_swap (Pi.single (0 : Fin 2) 1) (Pi.single (1 : Fin 2) 1)]
  all_goals module

theorem contract22_pack13_basis (a b c d : A) (i j : Fin 2) :
    contract22 (pack13 a b c d (Pi.single i 1) (Pi.single j 1))=0 := by
  fin_cases i <;> fin_cases j
  all_goals simp only [pack13, map_add, map_sub, contract22_fourth,
    AlternatingFour.raw_apply, AlternatingThree.raw_apply, MultilinearMap.curryLeft_apply,
    toMultilinear, MultilinearMap.mk'_apply, Matrix.Fin.cons_vecCons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, raw22_pure]
  all_goals norm_num [SU2DoubletDuality.epsilon_apply, e0, e1, -sym_tmul,
    -ExteriorSquareTensorDescent.wedge_tmul]

theorem contract22_pack13 (a b c d : A) (y : Sym[ℂ]^2 B) :
    contract22 (pack13Linear a b c d y)=0 := by
  have h : ((contract22 (A := A)).comp (pack13Linear a b c d)).comp (sym (A := B))=0 := by
    apply ((Pi.basisFun ℂ (Fin 2)).tensorProduct (Pi.basisFun ℂ (Fin 2))).ext
    rintro ⟨i,j⟩
    simp only [Module.Basis.tensorProduct_apply, Pi.basisFun_apply]
    change contract22 (pack13Linear a b c d (sym (Pi.single i 1 ⊗ₜ[ℂ] Pi.single j 1)))=0
    rw [pack13Linear_pure]
    exact contract22_pack13_basis a b c d i j
  have hs : (contract22 (A := A)).comp (pack13Linear a b c d)=0 := by
    apply SymmetricPower.ext
    intro v
    rw [← sym_eta v]
    exact LinearMap.congr_fun h (v 0 ⊗ₜ[ℂ] v 1)
  exact LinearMap.congr_fun hs y

theorem contract13_insert22 : (contract13 (A := A)).comp insert22=0 := by
  apply source22_ext
  intro a b c d
  change contract13 (insert22 (sym (wedge (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] wedge (c ⊗ₜ[ℂ] d))))=0
  rw [insert22_pure]
  simp only [map_add, map_sub, contract13_pack22, add_zero, sub_self]

theorem contract22_insert13 : (contract22 (A := A)).comp insert13=0 := by
  apply source13_ext
  intro a b c d y
  change contract22 (insert13 ((a ⊗ₜ[ℂ] cube b c d) ⊗ₜ[ℂ] y))=0
  rw [insert13_cube]
  simp only [map_add, map_sub, contract22_pack13, add_zero, sub_self]

theorem contract13_diagonal (a b c d : A) (s : B) :
    contract13 (fourth (a ⊗ₜ[ℂ] s) (b ⊗ₜ[ℂ] s) (c ⊗ₜ[ℂ] s) (d ⊗ₜ[ℂ] s))=0 := by
  have hs : SU2DoubletDuality.epsilon s s=0 := by simp [SU2DoubletDuality.epsilon_apply, mul_comm]
  simp only [contract13_fourth,
    AlternatingFour.raw_apply, AlternatingThree.raw_apply, MultilinearMap.curryLeft_apply,
    toMultilinear, MultilinearMap.mk'_apply, Matrix.Fin.cons_vecCons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, raw13_pure,
    hs, zero_smul, add_zero, sub_self]

theorem contract22_diagonal (a b c d : A) (s : B) :
    contract22 (fourth (a ⊗ₜ[ℂ] s) (b ⊗ₜ[ℂ] s) (c ⊗ₜ[ℂ] s) (d ⊗ₜ[ℂ] s))=0 := by
  have hs : SU2DoubletDuality.epsilon s s=0 := by simp [SU2DoubletDuality.epsilon_apply, mul_comm]
  simp only [contract22_fourth,
    AlternatingFour.raw_apply, AlternatingThree.raw_apply, MultilinearMap.curryLeft_apply,
    toMultilinear, MultilinearMap.mk'_apply, Matrix.Fin.cons_vecCons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, raw22_pure,
    hs, zero_mul, zero_smul, add_zero, sub_self]

theorem column_zero_of_diagonal {N : Type*} [AddCommGroup N] [Module ℂ N]
    (f : Total (A := A) →ₗ[ℂ] N)
    (h : ∀ a b c d s, f (fourth (a ⊗ₜ[ℂ] s) (b ⊗ₜ[ℂ] s) (c ⊗ₜ[ℂ] s) (d ⊗ₜ[ℂ] s))=0) :
    f.comp (ExteriorSymmetricColumn.column 4)=0 := by
  apply TensorProduct.ext'
  intro x y
  have hx : (f.comp (ExteriorSymmetricColumn.column 4)).comp ((TensorProduct.mk ℂ _ _).flip y)=0 := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro a
    have hy : (f.comp (ExteriorSymmetricColumn.column 4)).comp
        (TensorProduct.mk ℂ _ _ (exteriorPower.ιMulti ℂ 4 a))=0 := by
      apply SymmetricPurePowers.ext
      intro s
      change f (ExteriorSymmetricColumn.column 4
        (exteriorPower.ιMulti ℂ 4 a ⊗ₜ[ℂ] SymmetricPower.tprod ℂ (fun _ => s)))=0
      rw [ExteriorSymmetricColumn.diagonal, ← fourth_eta]
      exact h (a 0) (a 1) (a 2) (a 3) s
    exact LinearMap.congr_fun hy y
  exact LinearMap.congr_fun hx x

theorem contract13_column : (contract13 (A := A)).comp (ExteriorSymmetricColumn.column 4)=0 :=
  column_zero_of_diagonal _ contract13_diagonal

theorem contract22_column : (contract22 (A := A)).comp (ExteriorSymmetricColumn.column 4)=0 :=
  column_zero_of_diagonal _ contract22_diagonal

theorem retract211_insertK22 (x : K22 (A := A)) : retract211 (insertK22 x)=0 := by
  change (128 : ℂ)⁻¹ • TensorProduct.map project211 LinearMap.id
    (contract13 (insert22 x.val))=0
  have h := LinearMap.congr_fun (contract13_insert22 (A := A)) x.val
  change contract13 (insert22 x.val)=0 at h
  rw [h, map_zero, smul_zero]

theorem retractK22_insert211 (x : K211 (A := A) ⊗[ℂ] Sym[ℂ]^2 B) :
    retractK22 (insert211 x)=0 := by
  have h := LinearMap.congr_fun (contract22_insert13 (A := A))
    (TensorProduct.map (K211 (A := A)).subtype LinearMap.id x)
  change contract22 (insert211 x)=0 at h
  change (288 : ℂ)⁻¹ • project22 (contract22 (insert211 x))=0
  rw [h, map_zero, smul_zero]

theorem retract211_column (x : ExteriorFourthColumn.Column (A := A) (B := B)) :
    retract211 (ExteriorSymmetricColumn.column 4 x)=0 := by
  change (128 : ℂ)⁻¹ • TensorProduct.map project211 LinearMap.id
    (contract13 (ExteriorSymmetricColumn.column 4 x))=0
  have h := LinearMap.congr_fun (contract13_column (A := A)) x
  change contract13 (ExteriorSymmetricColumn.column 4 x)=0 at h
  rw [h, map_zero, smul_zero]

theorem retractK22_column (x : ExteriorFourthColumn.Column (A := A) (B := B)) :
    retractK22 (ExteriorSymmetricColumn.column 4 x)=0 := by
  change (288 : ℂ)⁻¹ • project22 (contract22 (ExteriorSymmetricColumn.column 4 x))=0
  have h := LinearMap.congr_fun (contract22_column (A := A)) x
  change contract22 (ExteriorSymmetricColumn.column 4 x)=0 at h
  rw [h, map_zero, smul_zero]

end
end Math.ExteriorFourthDoubletCross
