import Mathlib.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Complex.Basic

/-! Entrywise access to certified equivariant coordinate matrices. -/
namespace Math.MatrixIntertwiner
set_option autoImplicit false
noncomputable section
open Representation

variable {H J K : Type*} [Group H] [Fintype J] [Fintype K]
  [DecidableEq J] [DecidableEq K]
  (a : Representation ℂ H (J → ℂ)) (b : Representation ℂ H (K → ℂ))

def ofMatrix (c : Matrix K J ℂ)
    (hc : ∀ g v, c.mulVec (a g v) = b g (c.mulVec v)) : IntertwiningMap a b :=
  (Matrix.toLin' c).intertwiningMap_of_isIntertwiningMap a b
    (by intro g v; simpa only [Matrix.toLin'_apply] using hc g v)

omit [Fintype K] [DecidableEq K] in
@[simp] theorem apply (c : Matrix K J ℂ)
    (hc : ∀ g v, c.mulVec (a g v) = b g (c.mulVec v)) (v : J → ℂ) :
    ofMatrix a b c hc v = c.mulVec v := rfl

omit [Fintype K] [DecidableEq K] in
theorem entry (c : Matrix K J ℂ)
    (hc : ∀ g v, c.mulVec (a g v) = b g (c.mulVec v)) (e : K) (mu : J) :
    ofMatrix a b c hc (Pi.single mu 1) e = c e mu := by
  rw [apply, Matrix.mulVec_single_one]
  rfl

end
end Math.MatrixIntertwiner
