import Math.RepresentationTheory.Tensors.TwoComponentTensorUniqueness
import Mathlib.LinearAlgebra.UnitaryGroup

/-! The exhaustive triplet contraction for actual SL(2,C) and SU(2). -/
namespace Math.TwoComponentContractions
set_option autoImplicit false
noncomputable section
open Representation TwoComponentSymmetricTensor TwoComponentTensorUniqueness Matrix

def slDiagonal : TwoComponentSymmetricTensor.Group :=
  ⟨!![2,0;0,1/2], by norm_num [Matrix.det_fin_two]⟩
def slMixer : TwoComponentSymmetricTensor.Group :=
  ⟨!![1,1;1,2], by norm_num [Matrix.det_fin_two]⟩

theorem sl_unique (f : Coefficient (MonoidHom.id TwoComponentSymmetricTensor.Group)) :
    f = value _ f 0 0 0 • restrictedPair (MonoidHom.id _) := by
  apply unique _ slDiagonal slMixer 2 (1/2) 1 1 1 2 rfl _ rfl
    (by norm_num) (by norm_num) (by norm_num) f
  intro i j k h
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num [Allowed, Fin.ext_iff] at h
  all_goals norm_num

abbrev WeakGroup := Matrix.specialUnitaryGroup (Fin 2) ℂ

def weakToSL : WeakGroup →* TwoComponentSymmetricTensor.Group where
  toFun g := ⟨g.val, g.prop.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def weakDiagonal : WeakGroup :=
  ⟨!![(3+4*Complex.I)/5,0;0,(3-4*Complex.I)/5], by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
          map_ofNat, Complex.ext_iff, Complex.mul_re, Complex.mul_im]
    · norm_num [Matrix.det_fin_two, Complex.ext_iff, Complex.mul_re, Complex.mul_im]⟩

def weakMixer : WeakGroup :=
  ⟨!![3/5,4/5;-4/5,3/5], by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, map_ofNat]
    · norm_num [Matrix.det_fin_two]⟩

theorem weak_unique (f : Coefficient weakToSL) :
    f = value _ f 0 0 0 • restrictedPair weakToSL := by
  apply unique _ weakDiagonal weakMixer ((3+4*Complex.I)/5) ((3-4*Complex.I)/5)
    (3/5) (4/5) (-4/5) (3/5) rfl _ rfl
    (by norm_num) (by norm_num) (by norm_num) f
  intro i j k h
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num [Allowed, Fin.ext_iff] at h
  all_goals norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im, pow_two]

end
end Math.TwoComponentContractions
