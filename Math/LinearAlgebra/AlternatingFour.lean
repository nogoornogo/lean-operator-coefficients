import Math.LinearAlgebra.AlternatingThree
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! A structured universal four-slot alternator. This acts on arbitrary
vectors and never enumerates a representation basis. -/
namespace Math.AlternatingFour
set_option autoImplicit false
noncomputable section
variable {V N : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup N] [Module ℂ N]

def three : MultilinearMap ℂ (fun _ : Fin 3 => V) N →ₗ[ℂ]
    MultilinearMap ℂ (fun _ : Fin 3 => V) N where
  toFun := AlternatingThree.raw
  map_add' f g := by ext v; simp [AlternatingThree.raw]; module
  map_smul' z f := by ext v; simp [AlternatingThree.raw]; module

def tail (f : MultilinearMap ℂ (fun _ : Fin 4 => V) N) :
    MultilinearMap ℂ (fun _ : Fin 4 => V) N :=
  (three.comp f.curryLeft).uncurryLeft

private def p1 : Equiv.Perm (Fin 4) := Equiv.swap 0 1
private def p2 : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 0 1
private def p3 : Equiv.Perm (Fin 4) := Equiv.swap 2 3 * Equiv.swap 1 2 * Equiv.swap 0 1

def raw (f : MultilinearMap ℂ (fun _ : Fin 4 => V) N) :
    MultilinearMap ℂ (fun _ : Fin 4 => V) N :=
  tail f-(tail f).domDomCongr p1+(tail f).domDomCongr p2-(tail f).domDomCongr p3

theorem raw_apply (f : MultilinearMap ℂ (fun _ : Fin 4 => V) N) (v : Fin 4 → V) :
    raw f v=AlternatingThree.raw (f.curryLeft (v 0)) ![v 1,v 2,v 3]-
      AlternatingThree.raw (f.curryLeft (v 1)) ![v 0,v 2,v 3]+
      AlternatingThree.raw (f.curryLeft (v 2)) ![v 0,v 1,v 3]-
      AlternatingThree.raw (f.curryLeft (v 3)) ![v 0,v 1,v 2] := by
  have h0 : Fin.tail v=![v 1,v 2,v 3] := by ext i; fin_cases i <;> rfl
  have h1 : Fin.tail (fun i => v (p1 i))=![v 0,v 2,v 3] := by ext i; fin_cases i <;> rfl
  have h2 : Fin.tail (fun i => v (p2 i))=![v 0,v 1,v 3] := by ext i; fin_cases i <;> rfl
  have h3 : Fin.tail (fun i => v (p3 i))=![v 0,v 1,v 2] := by ext i; fin_cases i <;> rfl
  simp only [raw, add_apply, sub_apply, MultilinearMap.domDomCongr_apply,
    tail, LinearMap.uncurryLeft_apply, LinearMap.comp_apply, three, LinearMap.coe_mk,
    AddHom.coe_mk, h0, h1, h2, h3]
  change _=_
  rfl

def alternating (f : MultilinearMap ℂ (fun _ : Fin 4 => V) N) :
    V [⋀^Fin 4]→ₗ[ℂ] N where
  toMultilinearMap := raw f
  map_eq_zero_of_eq' v i j hij hne := by
    change raw f v=0
    rw [raw_apply]
    simp only [AlternatingThree.raw_apply, MultilinearMap.curryLeft_apply, Matrix.Fin.cons_vecCons,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    fin_cases i <;> fin_cases j <;> try exact (hne rfl).elim
    all_goals dsimp at hij
    all_goals rw [hij]
    all_goals module

end
end Math.AlternatingFour
