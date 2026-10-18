import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Complex.Basic

/-! Polynomial uniqueness on the conjugate-diagonal real form. -/
namespace Math.PolynomialRealForm
set_option autoImplicit false
noncomputable section
open MvPolynomial

def coordinates : Fin 2 → MvPolynomial (Fin 2) ℂ := ![X 0 + C Complex.I * X 1, X 0 - C Complex.I * X 1]

theorem eval_coordinates (p : MvPolynomial (Fin 2) ℂ) (x y : ℂ) :
    eval ![x,y] (eval₂ C coordinates p) = eval ![x+Complex.I*y,x-Complex.I*y] p := by
  rw [eval_eval₂]
  congr 1
  · ext a; simp
  · funext i
    fin_cases i <;> simp [coordinates]

theorem zero_of_conjugate_diagonal (p : MvPolynomial (Fin 2) ℂ)
    (h : ∀ z : ℂ, eval ![z,star z] p = 0) : p = 0 := by
  let q := eval₂ C coordinates p
  have hq : q = 0 := by
    apply funext_set (fun _ : Fin 2 => Set.range (fun x : ℝ => (x : ℂ)))
      (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
    intro a ha
    obtain ⟨x,hx⟩ := ha 0 (Set.mem_univ _)
    obtain ⟨y,hy⟩ := ha 1 (Set.mem_univ _)
    have he : a = ![(x : ℂ),(y : ℂ)] := by
      funext i; fin_cases i <;> simp [← hx, ← hy]
    rw [he]
    change eval ![(x : ℂ),(y : ℂ)] (eval₂ C coordinates p) = eval ![(x : ℂ),(y : ℂ)] 0
    rw [eval_coordinates]
    simpa [sub_eq_add_neg] using h ((x : ℂ)+Complex.I*(y : ℂ))
  apply MvPolynomial.funext
  intro a
  let x := (a 0 + a 1)/2
  let y := (a 0 - a 1)/(2*Complex.I)
  have he : ![x+Complex.I*y,x-Complex.I*y] = a := by
    funext i
    fin_cases i
    · change x + Complex.I*y = a 0
      dsimp [x,y]
      field_simp
      ring
    · change x - Complex.I*y = a 1
      dsimp [x,y]
      field_simp
      ring
  have hh := congrArg (eval ![x,y]) hq
  rw [eval_coordinates, he] at hh
  exact hh

end
end Math.PolynomialRealForm
