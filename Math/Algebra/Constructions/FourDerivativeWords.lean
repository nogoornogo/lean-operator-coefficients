import Math.Algebra.Constructions.ColoredQuarticWords
import Mathlib.LinearAlgebra.Multilinear.Basic

/-! Four independently variable polynomial factors, before field substitution. -/
namespace Math.FourDerivativeWords
set_option autoImplicit false
noncomputable section
variable {A : Type*} [CommRing A] [Algebra ℂ A]
  (D : Fin 4 → Derivation ℂ A A)

def word (r : Fin 5) (i j k l : Fin 4) (v : Fin 4 → A) : A := match r with
  | 0 => v 0*v 1*v 2*D i (D j (D k (D l (v 3))))
  | 1 => v 0*v 1*D i (D j (D k (v 2)))*D l (v 3)
  | 2 => v 0*v 1*D i (D j (v 2))*D k (D l (v 3))
  | 3 => v 0*D i (D j (v 1))*D k (v 2)*D l (v 3)
  | 4 => D i (v 0)*D j (v 1)*D k (v 2)*D l (v 3)

def multilinear (r : Fin 5) (i j k l : Fin 4) : MultilinearMap ℂ (fun _ : Fin 4 => A) A :=
  MultilinearMap.mk' (word D r i j k l)
    (by intro v t x y; fin_cases r <;> fin_cases t <;>
      simp [word,Function.update,Fin.ext_iff,map_add,mul_add,add_mul])
    (by intro v t z x; fin_cases r <;> fin_cases t <;>
      simp [word,Function.update,Fin.ext_iff,Derivation.map_smul])

theorem multilinear_apply (r : Fin 5) (i j k l : Fin 4) (v : Fin 4 → A) :
    multilinear D r i j k l v = word D r i j k l v := rfl

theorem transport_word (F : A →ₐ[ℂ] A) (hD : ∀ i p, F (D i p) = D i (F p))
    (r : Fin 5) (i j k l : Fin 4) (v : Fin 4 → A) :
    F (word D r i j k l v) = word D r i j k l (fun t => F (v t)) := by
  fin_cases r <;> simp only [word,map_mul,hD]

end
end Math.FourDerivativeWords
