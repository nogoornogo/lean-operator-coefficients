import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-! A six-term universal alternator in three slots. No finite-dimensional
basis or list of representation coefficients is expanded. -/
namespace Math.AlternatingThree
set_option autoImplicit false
noncomputable section
variable {V N : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup N] [Module ℂ N]

private def p01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
private def p02 : Equiv.Perm (Fin 3) := Equiv.swap 0 2
private def p12 : Equiv.Perm (Fin 3) := Equiv.swap 1 2

def raw (f : MultilinearMap ℂ (fun _ : Fin 3 => V) N) :
    MultilinearMap ℂ (fun _ : Fin 3 => V) N :=
  f-f.domDomCongr p01-f.domDomCongr p02-f.domDomCongr p12+
    f.domDomCongr (p01*p12)+f.domDomCongr (p12*p01)

theorem raw_apply (f : MultilinearMap ℂ (fun _ : Fin 3 => V) N) (v : Fin 3 → V) :
    raw f v = f ![v 0,v 1,v 2]-f ![v 1,v 0,v 2]-f ![v 2,v 1,v 0]-
      f ![v 0,v 2,v 1]+f ![v 1,v 2,v 0]+f ![v 2,v 0,v 1] := by
  have hv : (![v 0,v 1,v 2] : Fin 3 → V)=v := by ext i; fin_cases i <;> rfl
  have h01 : (fun i => v (p01 i))=![v 1,v 0,v 2] := by ext i; fin_cases i <;> rfl
  have h02 : (fun i => v (p02 i))=![v 2,v 1,v 0] := by ext i; fin_cases i <;> rfl
  have h12 : (fun i => v (p12 i))=![v 0,v 2,v 1] := by ext i; fin_cases i <;> rfl
  have hc : (fun i => v ((p01*p12) i))=![v 1,v 2,v 0] := by ext i; fin_cases i <;> rfl
  have hd : (fun i => v ((p12*p01) i))=![v 2,v 0,v 1] := by ext i; fin_cases i <;> rfl
  simp only [raw,add_apply,sub_apply,
    MultilinearMap.domDomCongr_apply,h01,h02,h12,hc,hd,hv]

def alternating (f : MultilinearMap ℂ (fun _ : Fin 3 => V) N) : V [⋀^Fin 3]→ₗ[ℂ] N where
  toMultilinearMap := raw f
  map_eq_zero_of_eq' v i j hij hne := by
    change raw f v=0
    rw [raw_apply]
    fin_cases i <;> fin_cases j <;> try exact (hne rfl).elim
    all_goals dsimp at hij
    all_goals rw [hij]
    all_goals abel

end
end Math.AlternatingThree
