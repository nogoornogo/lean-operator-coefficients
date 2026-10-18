import Math.LinearAlgebra.AlternatingFour
import Math.LinearAlgebra.ExteriorFourthKernels
import Math.LinearAlgebra.TensorFourthMultilinear

/-! Short quartic shuffle maps, constructed by alternation. The
identities hold on arbitrary vectors, independently of source dimension. -/
namespace Math.ExteriorFourthShuffle
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open TensorSquareQuotients ExteriorCubeHook ExteriorFourthKernels
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
variable {A : Type*} [AddCommGroup A] [Module ℂ A]
@[reducible] local instance : AddCommGroup (Source22 (A := A)) :=
  Module.addCommMonoidToAddCommGroup ℂ

theorem cube_reverse (a b c : A) : cube c b a= -cube a b c := by
  rw [cube_swap01 b c a, ← cube_cycle b c a]

theorem cube_rotate (a b c : A) : cube b c a=cube a b c :=
  (cube_cycle b c a).symm

def delta13 : Fourth (A := A) →ₗ[ℂ] Source13 (A := A) :=
  (6 : ℂ)⁻¹ • exteriorPower.alternatingMapLinearEquiv
    (AlternatingFour.alternating (raw13 (A := A)))

theorem delta13_pure (a b c d : A) : delta13 (fourth a b c d)=
    a ⊗ₜ[ℂ] cube b c d-b ⊗ₜ[ℂ] cube a c d+
      c ⊗ₜ[ℂ] cube a b d-d ⊗ₜ[ℂ] cube a b c := by
  change (6 : ℂ)⁻¹ • exteriorPower.alternatingMapLinearEquiv
    (AlternatingFour.alternating (raw13 (A := A))) (exteriorPower.ιMulti ℂ 4 ![a,b,c,d])=_
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change (6 : ℂ)⁻¹ • AlternatingFour.raw (raw13 (A := A)) ![a,b,c,d]=_
  rw [AlternatingFour.raw_apply]
  simp only [AlternatingThree.raw_apply, MultilinearMap.curryLeft_apply,
    raw13, MultilinearMap.mk'_apply, Matrix.Fin.cons_vecCons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
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
    cube_cycle a b c]
  simp only [TensorProduct.tmul_neg]
  module

theorem sym_neg_left {V : Type*} [AddCommGroup V] [Module ℂ V] (x y : V) :
    sym ((-x) ⊗ₜ[ℂ] y)=(-1 : ℂ) • sym (x ⊗ₜ[ℂ] y) := by
  rw [show -x=(-1 : ℂ) • x from (neg_one_smul ℂ x).symm,
    TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul]

theorem sym_neg_right {V : Type*} [AddCommGroup V] [Module ℂ V] (x y : V) :
    sym (x ⊗ₜ[ℂ] (-y))=(-1 : ℂ) • sym (x ⊗ₜ[ℂ] y) := by
  rw [show -y=(-1 : ℂ) • y from (neg_one_smul ℂ y).symm,
    TensorProduct.tmul_smul, map_smul]

def delta22 : Fourth (A := A) →ₗ[ℂ] Source22 (A := A) :=
  (8 : ℂ)⁻¹ • exteriorPower.alternatingMapLinearEquiv
    (AlternatingFour.alternating (raw22 (A := A)))

theorem delta22_pure (a b c d : A) : delta22 (fourth a b c d)=
    sym (wedge (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] wedge (c ⊗ₜ[ℂ] d))-
      sym (wedge (a ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] d))+
      sym (wedge (a ⊗ₜ[ℂ] d) ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] c)) := by
  change (8 : ℂ)⁻¹ • exteriorPower.alternatingMapLinearEquiv
    (AlternatingFour.alternating (raw22 (A := A))) (exteriorPower.ιMulti ℂ 4 ![a,b,c,d])=_
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change (8 : ℂ)⁻¹ • AlternatingFour.raw (raw22 (A := A)) ![a,b,c,d]=_
  rw [AlternatingFour.raw_apply]
  simp only [AlternatingThree.raw_apply, MultilinearMap.curryLeft_apply,
    raw22, MultilinearMap.mk'_apply, Matrix.Fin.cons_vecCons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  simp only [ExteriorSquareTensorDescent.wedge_swap a b,
    ExteriorSquareTensorDescent.wedge_swap a c, ExteriorSquareTensorDescent.wedge_swap a d,
    ExteriorSquareTensorDescent.wedge_swap b c, ExteriorSquareTensorDescent.wedge_swap b d,
    ExteriorSquareTensorDescent.wedge_swap c d]
  simp only [sym_neg_left, sym_neg_right, smul_smul]
  simp only [sym_swap (wedge (a ⊗ₜ[ℂ] b)) (wedge (c ⊗ₜ[ℂ] d)),
    sym_swap (wedge (a ⊗ₜ[ℂ] c)) (wedge (b ⊗ₜ[ℂ] d)),
    sym_swap (wedge (a ⊗ₜ[ℂ] d)) (wedge (b ⊗ₜ[ℂ] c))]
  module

def cubeSection : (⋀[ℂ]^3 A) →ₗ[ℂ] (A ⊗[ℂ] (A ⊗[ℂ] A)) :=
  exteriorPower.alternatingMapLinearEquiv
    (AlternatingThree.alternating
      (TensorCubeMultilinear.toMultilinear (LinearMap.id : A ⊗[ℂ] (A ⊗[ℂ] A) →ₗ[ℂ] _)))

theorem cubeSection_pure (a b c : A) : cubeSection (cube a b c)=
    a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] c)-b ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] c)-c ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] a)-
      a ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] b)+b ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] a)+c ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] b) := by
  rw [cube, cubeSection, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact AlternatingThree.raw_apply _ _

end
end Math.ExteriorFourthShuffle
