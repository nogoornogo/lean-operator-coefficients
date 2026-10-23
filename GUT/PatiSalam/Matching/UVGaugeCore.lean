import GUT.PatiSalam.Matching.InvariantAction
import GUT.PatiSalam.Matching.UVComponent

open Physics

/-! Ordered internal gauge kernel of Eq.(19); no fermionic statistics quotient. -/
namespace GUT.PatiSalam.UVGaugeCore
set_option autoImplicit false
noncomputable section
open StandardModelEmbedding ComponentRepresentations SMEpsilonTensor
open scoped Matrix

def eps4 (a b c d : Four) : ℂ := Matrix.det (Matrix.of ![a,b,c,d])

theorem eps4_invariant (g : Matrix (Fin 4) (Fin 4) ℂ) (hg : Matrix.det g=1)
    (a b c d : Four) : eps4 (g.mulVec a) (g.mulVec b) (g.mulVec c) (g.mulVec d) = eps4 a b c d := by
  have he : Matrix.of ![g.mulVec a,g.mulVec b,g.mulVec c,g.mulVec d] =
      (Matrix.of ![a,b,c,d]) * g.transpose := by
    ext i j
    fin_cases i <;> simp [Matrix.mulVec,dotProduct,Matrix.mul_apply,mul_comm]
  rw [eps4,he,Matrix.det_mul,Matrix.det_transpose,hg,mul_one]
  rfl

def core (a b c d : Four) (i j k l : Two) := eps4 a b c d * eps2 i j * eps2 k l

theorem core_invariant (g : PSGroup) (a b c d : Four) (i j k l : Two)
    (fermion : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    core (four g a) (four g b) (four g c) (four g d)
      (fermion.val.mulVec i) (fermion.val.mulVec j) (right g k) (right g l) =
      core a b c d i j k l := by
  change eps4 (g.1.val.mulVec a) (g.1.val.mulVec b) (g.1.val.mulVec c) (g.1.val.mulVec d) *
    eps2 (fermion.val.mulVec i) (fermion.val.mulVec j) *
    eps2 (g.2.2.val.mulVec k) (g.2.2.val.mulVec l) = _
  rw [eps4_invariant _ g.1.prop.2,eps2_invariant _ fermion.prop.2,
    eps2_invariant _ g.2.2.prop.2]
  rfl

theorem color_coordinates (a : Color) : colorIn a = ![a 0,a 1,a 2,0] := by
  ext i
  fin_cases i
  · exact colorIn_color a 0
  · exact colorIn_color a 1
  · exact colorIn_color a 2
  · exact colorIn_lepton a 0

theorem lepton_coordinates : leptonIn (1:ℂ) = ![0,0,0,1] := by
  ext i
  fin_cases i
  · exact leptonIn_color 1 0
  · exact leptonIn_color 1 1
  · exact leptonIn_color 1 2
  · exact leptonIn_lepton 1 0

theorem eps4_color (a b c : Color) :
    eps4 (colorIn a) (colorIn b) (colorIn c) (leptonIn 1) = eps3 a b c := by
  rw [color_coordinates,color_coordinates,color_coordinates,lepton_coordinates]
  unfold eps4
  rw [Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix,Fin.succAbove,eps3]
  ring

theorem eps4_swap_last (a b c d : Four) : eps4 a b d c = -eps4 a b c d := by
  have he : (Matrix.of ![a,b,c,d]).submatrix (Equiv.swap (2:Fin 4) 3) id =
      Matrix.of ![a,b,d,c] := by
    ext i j
    fin_cases i <;> simp [Matrix.submatrix,Equiv.swap_apply_def]
  have h := Matrix.det_permute (Equiv.swap (2:Fin 4) 3) (Matrix.of ![a,b,c,d])
  rw [he,Equiv.Perm.sign_swap (show (2:Fin 4) ≠ 3 by decide)] at h
  simpa [eps4] using h

def selected (a b c : Color) : ℂ :=
  core (colorIn a) (colorIn b) (colorIn c) (leptonIn 1)
    (weakBasis 1) (weakBasis 0) (weakBasis 1) (weakBasis 0) +
  core (colorIn b) (colorIn a) (colorIn c) (leptonIn 1)
    (weakBasis 0) (weakBasis 1) (weakBasis 1) (weakBasis 0) +
  core (colorIn a) (colorIn b) (leptonIn 1) (colorIn c)
    (weakBasis 1) (weakBasis 0) (weakBasis 0) (weakBasis 1) +
  core (colorIn b) (colorIn a) (leptonIn 1) (colorIn c)
    (weakBasis 0) (weakBasis 1) (weakBasis 0) (weakBasis 1)

theorem selected_four (a b c : Color) : selected a b c = 4 * eps3 a b c := by
  unfold selected core
  rw [eps4_swap_last (colorIn a) (colorIn b) (colorIn c) (leptonIn 1),eps4_swap_last (colorIn b) (colorIn a) (colorIn c) (leptonIn 1)]
  rw [eps4_color,eps4_color]
  simp [eps2,weakBasis,eps3]
  ring

theorem selected_basis (a b c : Fin 3) :
    selected (colorBasis a) (colorBasis b) (colorBasis c) = (UVComponent.component a b c : ℂ) := by
  rw [selected_four,UVComponent.component_eq_four]
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [eps3,colorBasis,Pi.single_apply,UVComponent.epsilon,
      List.range_succ,List.countP,List.countP.go,List.drop,List.map,List.sum_cons]

def leftSelected (a b c : Color) (i j : Two) : ℂ :=
  core (colorIn a) (colorIn b) (colorIn c) (leptonIn 1) i j (weakBasis 1) (weakBasis 0) +
  core (colorIn a) (colorIn b) (leptonIn 1) (colorIn c) i j (weakBasis 0) (weakBasis 1)

theorem leftSelected_eq (a b c : Color) (i j : Two) :
    leftSelected a b c i j = -2 * eps3 a b c * eps2 i j := by
  unfold leftSelected core
  rw [eps4_swap_last (colorIn a) (colorIn b) (colorIn c) (leptonIn 1),eps4_color]
  simp [eps2,weakBasis]
  ring

theorem selected_prefactor (C Lambda v : ℂ) (hL : Lambda ≠ 0) (a b c : Color) :
    (C/(4*Lambda))*v*selected a b c = (C*v/Lambda)*eps3 a b c := by
  rw [selected_four]
  field_simp

theorem rr_invariant (g : PSGroup) (a b c d : Four) (i j k l : Two) :
    core (four g a) (four g b) (four g c) (four g d)
      (right g i) (right g j) (right g k) (right g l) = core a b c d i j k l :=
  core_invariant g a b c d i j k l g.2.2

theorem lr_invariant (g : PSGroup) (a b c d : Four) (i j k l : Two) :
    core (four g a) (four g b) (four g c) (four g d)
      (left g i) (left g j) (right g k) (right g l) = core a b c d i j k l :=
  core_invariant g a b c d i j k l g.2.1

end
end GUT.PatiSalam.UVGaugeCore
