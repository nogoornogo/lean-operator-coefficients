import Math.LinearAlgebra.Exterior.ExteriorFourthShuffle
import Math.LinearAlgebra.Exterior.ExteriorFourthColumn
import Math.RepresentationTheory.SU2.SU2SymmetricEmbeddings
import Math.RepresentationTheory.SU2.SU2DoubletDuality

/-! Actual insertion and contraction maps for the two remaining quartic
doublet components. The source color space is arbitrary. -/
namespace Math.ExteriorFourthDoublet
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open TensorSquareQuotients ExteriorCubeHook ExteriorFourthKernels ExteriorFourthShuffle
open TensorFourthMultilinear
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {A : Type*} [AddCommGroup A] [Module ℂ A]
abbrev B := WeakDoubletScalars.Doublet
abbrev Target13 := Source13 (A := A) ⊗[ℂ] Sym[ℂ]^2 B
abbrev Total := ⋀[ℂ]^4 (A ⊗[ℂ] B)
@[reducible] local instance : AddCommGroup (Target13 (A := A)) := inferInstance
@[reducible] local instance : AddCommGroup (Source22 (A := A)) :=
  Module.addCommMonoidToAddCommGroup ℂ

def e0 : B := Pi.single 0 1
def e1 : B := Pi.single 1 1

def colorContract13 : Tensor (V := A) →ₗ[ℂ] Source13 (A := A) :=
  TensorProduct.map LinearMap.id
    (TensorCubeMultilinear.fromMultilinear (exteriorPower.ιMulti ℂ 3).toMultilinearMap)

def spinContract13 : Tensor (V := B) →ₗ[ℂ] Sym[ℂ]^2 B :=
  sym.comp ((TensorProduct.lid ℂ (B ⊗[ℂ] B)).toLinearMap.comp
    ((TensorProduct.map (TensorProduct.lift SU2DoubletDuality.epsilon) LinearMap.id).comp
      (TensorProduct.assoc ℂ B B (B ⊗[ℂ] B)).symm.toLinearMap))

def raw13 : Tensor (V := A ⊗[ℂ] B) →ₗ[ℂ] Target13 (A := A) :=
  (TensorProduct.map colorContract13 spinContract13).comp ExteriorFourthColumn.regroup.toLinearMap

theorem raw13_pure (a b c d : A) (s t u v : B) :
    raw13 ((a ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] ((b ⊗ₜ[ℂ] t) ⊗ₜ[ℂ]
      ((c ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] (d ⊗ₜ[ℂ] v))))=
      SU2DoubletDuality.epsilon s t • ((a ⊗ₜ[ℂ] cube b c d) ⊗ₜ[ℂ] sym (u ⊗ₜ[ℂ] v)) := by
  change (a ⊗ₜ[ℂ] cube b c d) ⊗ₜ[ℂ] sym (SU2DoubletDuality.epsilon s t • (u ⊗ₜ[ℂ] v))=_
  rw [map_smul, TensorProduct.tmul_smul]

def contract13 : Total (A := A) →ₗ[ℂ] Target13 (A := A) :=
  exteriorPower.alternatingMapLinearEquiv
    (AlternatingFour.alternating (toMultilinear (raw13 (A := A))))

theorem contract13_fourth (x y z w : A ⊗[ℂ] B) :
    contract13 (fourth x y z w)=AlternatingFour.raw (toMultilinear raw13) ![x,y,z,w] := by
  rw [fourth, contract13, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

def spinInsert13 : Sym[ℂ]^2 B →ₗ[ℂ] Tensor (V := B) :=
  (TensorProduct.assoc ℂ B B (B ⊗[ℂ] B)).toLinearMap.comp
    ((TensorProduct.mk ℂ (B ⊗[ℂ] B) (B ⊗[ℂ] B)
      (e0 ⊗ₜ[ℂ] e1-e1 ⊗ₜ[ℂ] e0)).comp symmetricSection)

def insert13 : Target13 (A := A) →ₗ[ℂ] Total (A := A) :=
  (fromMultilinear (exteriorPower.ιMulti ℂ 4).toMultilinearMap).comp
    (ExteriorFourthColumn.regroup.symm.toLinearMap.comp
      (TensorProduct.map (TensorProduct.map LinearMap.id cubeSection) spinInsert13))

def pack13 (a b c d : A) (s t : B) : Total (A := A) :=
  fourth (a ⊗ₜ[ℂ] e0) (b ⊗ₜ[ℂ] e1) (c ⊗ₜ[ℂ] s) (d ⊗ₜ[ℂ] t)+
  fourth (a ⊗ₜ[ℂ] e0) (b ⊗ₜ[ℂ] e1) (c ⊗ₜ[ℂ] t) (d ⊗ₜ[ℂ] s)-
  fourth (a ⊗ₜ[ℂ] e1) (b ⊗ₜ[ℂ] e0) (c ⊗ₜ[ℂ] s) (d ⊗ₜ[ℂ] t)-
  fourth (a ⊗ₜ[ℂ] e1) (b ⊗ₜ[ℂ] e0) (c ⊗ₜ[ℂ] t) (d ⊗ₜ[ℂ] s)

theorem regroup_symm_pure (a b c d : A) (s t u v : B) :
    (ExteriorFourthColumn.regroup (A := A) (B := B)).symm
      ((a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d))) ⊗ₜ[ℂ] (s ⊗ₜ[ℂ] (t ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] v))))=
    (a ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] ((b ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] ((c ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] (d ⊗ₜ[ℂ] v))) := rfl

theorem insert13_pure (a b c d : A) (s t : B) :
    insert13 ((a ⊗ₜ[ℂ] cube b c d) ⊗ₜ[ℂ] sym (s ⊗ₜ[ℂ] t))=
      pack13 a b c d s t-pack13 a c b d s t-pack13 a d c b s t-
        pack13 a b d c s t+pack13 a c d b s t+pack13 a d b c s t := by
  simp only [insert13, LinearMap.comp_apply, TensorProduct.map_tmul,
    cubeSection_pure, spinInsert13, symmetricSection_pure, TensorProduct.mk_apply,
    TensorProduct.add_tmul, TensorProduct.sub_tmul, TensorProduct.tmul_add, TensorProduct.tmul_sub,
    map_add, map_sub, TensorProduct.assoc_tmul, LinearEquiv.coe_coe, LinearMap.id_apply]
  simp only [regroup_symm_pure, from_pure]
  unfold pack13 fourth
  module

theorem tmul_neg_scalar {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (x : V) (y : W) :
    x ⊗ₜ[ℂ] (-y)=(-1 : ℂ) • (x ⊗ₜ[ℂ] y) := by
  rw [show -y=(-1 : ℂ) • y from (neg_one_smul ℂ y).symm, TensorProduct.tmul_smul]

theorem contract13_pack13_basis (a b c d : A) (i j : Fin 2) :
    contract13 (pack13 a b c d (Pi.single i 1) (Pi.single j 1))=
    (16 : ℂ) • (((a ⊗ₜ[ℂ] cube b c d)+(b ⊗ₜ[ℂ] cube a c d)) ⊗ₜ[ℂ]
      sym (Pi.single i 1 ⊗ₜ[ℂ] Pi.single j 1)) := by
  fin_cases i <;> fin_cases j
  all_goals simp only [pack13, map_add, map_sub, contract13_fourth,
    AlternatingFour.raw_apply, AlternatingThree.raw_apply, MultilinearMap.curryLeft_apply,
    toMultilinear, MultilinearMap.mk'_apply, Matrix.Fin.cons_vecCons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, raw13_pure]
  all_goals norm_num [SU2DoubletDuality.epsilon_apply, e0, e1, -sym_tmul]
  all_goals simp only [cube_swap01 b c d,
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
    cube_cycle a b c,
    tmul_neg_scalar, TensorProduct.smul_tmul, TensorProduct.tmul_smul, TensorProduct.add_tmul,
    sym_swap (Pi.single (0 : Fin 2) 1) (Pi.single (1 : Fin 2) 1)]
  all_goals module

def pack13Linear (a b c d : A) : Sym[ℂ]^2 B →ₗ[ℂ] Total (A := A) :=
  (fromMultilinear (exteriorPower.ιMulti ℂ 4).toMultilinearMap).comp
    (ExteriorFourthColumn.regroup.symm.toLinearMap.comp
      ((TensorProduct.mk ℂ (Tensor (V := A)) (Tensor (V := B))
        (a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d)))).comp spinInsert13))

theorem pack13Linear_pure (a b c d : A) (s t : B) :
    pack13Linear a b c d (sym (s ⊗ₜ[ℂ] t))=pack13 a b c d s t := by
  simp only [pack13Linear, LinearMap.comp_apply, spinInsert13, symmetricSection_pure,
    TensorProduct.mk_apply, TensorProduct.sub_tmul,
    map_add, map_sub,
    TensorProduct.assoc_tmul, LinearEquiv.coe_coe, regroup_symm_pure, from_pure]
  unfold pack13 fourth
  module

theorem contract13_pack13 (a b c d : A) (y : Sym[ℂ]^2 B) :
    contract13 (pack13Linear a b c d y)=
      (16 : ℂ) • (((a ⊗ₜ[ℂ] cube b c d)+(b ⊗ₜ[ℂ] cube a c d)) ⊗ₜ[ℂ] y) := by
  have h : ((contract13 (A := A)).comp (pack13Linear a b c d)).comp (sym (A := B))=
      ((16 : ℂ) • TensorProduct.mk ℂ _ _
        ((a ⊗ₜ[ℂ] cube b c d)+(b ⊗ₜ[ℂ] cube a c d))).comp sym := by
    apply ((Pi.basisFun ℂ (Fin 2)).tensorProduct (Pi.basisFun ℂ (Fin 2))).ext
    rintro ⟨i,j⟩
    simp only [Module.Basis.tensorProduct_apply, Pi.basisFun_apply]
    change contract13 (pack13Linear a b c d (sym (Pi.single i 1 ⊗ₜ[ℂ] Pi.single j 1)))=_
    rw [pack13Linear_pure]
    exact contract13_pack13_basis a b c d i j
  have hs : (contract13 (A := A)).comp (pack13Linear a b c d)=
      (16 : ℂ) • TensorProduct.mk ℂ _ _
        ((a ⊗ₜ[ℂ] cube b c d)+(b ⊗ₜ[ℂ] cube a c d)) := by
    apply SymmetricPower.ext
    intro v
    rw [← sym_eta v]
    exact LinearMap.congr_fun h (v 0 ⊗ₜ[ℂ] v 1)
  exact LinearMap.congr_fun hs y

theorem insert13_cube (a b c d : A) (y : Sym[ℂ]^2 B) :
    insert13 ((a ⊗ₜ[ℂ] cube b c d) ⊗ₜ[ℂ] y)=
      pack13Linear a b c d y-pack13Linear a c b d y-pack13Linear a d c b y-
        pack13Linear a b d c y+pack13Linear a c d b y+pack13Linear a d b c y := by
  have h : (insert13 (A := A)).comp (TensorProduct.mk ℂ _ _ (a ⊗ₜ[ℂ] cube b c d))=
      pack13Linear a b c d-pack13Linear a c b d-pack13Linear a d c b-
        pack13Linear a b d c+pack13Linear a c d b+pack13Linear a d b c := by
    apply SymmetricPower.ext
    intro v
    change insert13 ((a ⊗ₜ[ℂ] cube b c d) ⊗ₜ[ℂ] sym (v 0 ⊗ₜ[ℂ] v 1))=_
    simp only [LinearMap.add_apply, LinearMap.sub_apply]
    rw [← sym_eta v]
    simp only [pack13Linear_pure]
    exact insert13_pure a b c d (v 0) (v 1)
  exact LinearMap.congr_fun h y

theorem source13_ext {N : Type*} [AddCommGroup N] [Module ℂ N]
    {f g : Target13 (A := A) →ₗ[ℂ] N}
    (h : ∀ a b c d y, f ((a ⊗ₜ[ℂ] cube b c d) ⊗ₜ[ℂ] y)=
      g ((a ⊗ₜ[ℂ] cube b c d) ⊗ₜ[ℂ] y)) : f=g := by
  apply TensorProduct.ext'
  intro x y
  have hy : f.comp ((TensorProduct.mk ℂ _ _).flip y)=g.comp ((TensorProduct.mk ℂ _ _).flip y) := by
    apply TensorProduct.ext'
    intro a z
    have ha : (f.comp ((TensorProduct.mk ℂ _ _).flip y)).comp (TensorProduct.mk ℂ _ _ a)=
        (g.comp ((TensorProduct.mk ℂ _ _).flip y)).comp (TensorProduct.mk ℂ _ _ a) := by
      apply exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro v
      change f ((a ⊗ₜ[ℂ] exteriorPower.ιMulti ℂ 3 v) ⊗ₜ[ℂ] y)=
        g ((a ⊗ₜ[ℂ] exteriorPower.ιMulti ℂ 3 v) ⊗ₜ[ℂ] y)
      rw [← cube_eta v]
      exact h a (v 0) (v 1) (v 2) y
    exact LinearMap.congr_fun ha z
  exact LinearMap.congr_fun hy x

theorem contract13_insert13 : (contract13 (A := A)).comp insert13=
    (128 : ℂ) • LinearMap.id-(32 : ℂ) •
      TensorProduct.map (delta13.comp multiply13) LinearMap.id := by
  apply source13_ext
  intro a b c d y
  change contract13 (insert13 ((a ⊗ₜ[ℂ] cube b c d) ⊗ₜ[ℂ] y))=_
  rw [insert13_cube]
  simp only [map_add, map_sub, contract13_pack13,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    TensorProduct.map_tmul, LinearMap.comp_apply, multiply13_pure, delta13_pure]
  simp only [cube_swap01 b c d, cube_swap12 b c d, cube_reverse b c d,
    cube_rotate b c d, cube_cycle b c d,
    cube_swap12 a c d, cube_swap12 a b d, cube_swap12 a b c,
    tmul_neg_scalar, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
    TensorProduct.add_tmul, TensorProduct.sub_tmul]
  module

@[reducible] local instance : AddCommGroup (K211 (A := A) ⊗[ℂ] Sym[ℂ]^2 B) := inferInstance

def insert211 : (K211 (A := A) ⊗[ℂ] Sym[ℂ]^2 B) →ₗ[ℂ] Total (A := A) :=
  insert13.comp (TensorProduct.map (K211 (A := A)).subtype LinearMap.id)

def retract211 : Total (A := A) →ₗ[ℂ] K211 (A := A) ⊗[ℂ] Sym[ℂ]^2 B :=
  (128 : ℂ)⁻¹ • (TensorProduct.map project211 LinearMap.id).comp contract13

theorem retract211_insert211 (x : K211 (A := A) ⊗[ℂ] Sym[ℂ]^2 B) :
    retract211 (insert211 x)=x := by
  have h : (retract211 (A := A)).comp insert211=LinearMap.id := by
    apply TensorProduct.ext'
    intro x y
    have hh := LinearMap.congr_fun (contract13_insert13 (A := A)) (x.val ⊗ₜ[ℂ] y)
    change contract13 (insert13 (x.val ⊗ₜ[ℂ] y))=
      (128 : ℂ) • (x.val ⊗ₜ[ℂ] y)-(32 : ℂ) • (delta13 (multiply13 x.val) ⊗ₜ[ℂ] y) at hh
    rw [show multiply13 x.val=0 from x.property, map_zero, TensorProduct.zero_tmul,
      smul_zero, sub_zero] at hh
    change (128 : ℂ)⁻¹ • TensorProduct.map project211 LinearMap.id
      (contract13 (insert13 (x.val ⊗ₜ[ℂ] y)))=x ⊗ₜ[ℂ] y
    rw [hh, map_smul, TensorProduct.map_tmul, project211_kernel, LinearMap.id_apply, smul_smul]
    norm_num
  exact LinearMap.congr_fun h x

theorem insert211_injective : Function.Injective (insert211 (A := A)) :=
  Function.LeftInverse.injective retract211_insert211

end
end Math.ExteriorFourthDoublet
