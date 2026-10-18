import Math.RepresentationTheory.ExteriorSquareCompression

/-! Coordinate block compression for exterior-square actions. -/
set_option autoImplicit false
namespace Math.ExteriorSquareBlock
noncomputable section
open ExteriorSquareCoordinates
variable (r : ℕ)

def includeFive : (Fin 5 → ℂ) →ₗ[ℂ] (Fin (5+r) → ℂ) where
  toFun x j := if h : j.val < 5 then x ⟨j.val,h⟩ else 0
  map_add' x y := by ext j; by_cases h : j.val < 5 <;> simp [h]
  map_smul' c x := by ext j; by_cases h : j.val < 5 <;> simp [h]

def restrictFive : (Fin (5+r) → ℂ) →ₗ[ℂ] (Fin 5 → ℂ) where
  toFun x i := x (Fin.castAdd r i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restrict_include (x : Fin 5 → ℂ) : restrictFive r (includeFive r x) = x := by
  ext i
  simp [restrictFive, includeFive]

def cut (X : Matrix (Fin (5+r)) (Fin (5+r)) ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  X.submatrix (Fin.castAdd r) (Fin.castAdd r)

theorem cut_action (X : Matrix (Fin (5+r)) (Fin (5+r)) ℂ) (x : Fin 5 → ℂ) :
    restrictFive r (Matrix.toLin' X (includeFive r x)) = Matrix.toLin' (cut r X) x := by
  ext i
  simp [restrictFive, includeFive, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_add, cut]

def embed : Space 5 →ₗ[ℂ] Space (5+r) := exteriorPower.map 2 (includeFive r)
def project : Space (5+r) →ₗ[ℂ] Space 5 := exteriorPower.map 2 (restrictFive r)

theorem project_embed : (project r).comp (embed r) = LinearMap.id := by
  rw [project, embed, ← exteriorPower.map_comp]
  have h : (restrictFive r).comp (includeFive r) = LinearMap.id :=
    LinearMap.ext (restrict_include r)
  rw [h, exteriorPower.map_id]

def coreAction (X : Matrix (Fin (5+r)) (Fin (5+r)) ℂ) : Module.End ℂ (Space 5) :=
  (project r).comp ((infinitesimal X).comp (embed r))

theorem coreAction_eq (X : Matrix (Fin (5+r)) (Fin (5+r)) ℂ) :
    coreAction r X = infinitesimal (cut r X) :=
  compress_infinitesimal (includeFive r) (restrictFive r) (restrict_include r)
    X (cut r X) (cut_action r X)

theorem cut_single (i j : Fin 5) :
    cut r (Matrix.single (Fin.castAdd r i) (Fin.castAdd r j) 1) = Matrix.single i j 1 := by
  ext a b
  simp [cut, Matrix.single_apply, Fin.ext_iff]

theorem cut_single_extra (i j : Fin (5+r)) (hj : 5 ≤ j.val) :
    cut r (Matrix.single i j 1) = 0 := by
  ext a b
  have h : j ≠ Fin.castAdd r b := by intro h; have := congrArg Fin.val h; simp at this; omega
  simp [cut, h]

theorem cut_single_extra_reverse (i j : Fin (5+r)) (hj : 5 ≤ j.val) :
    cut r (Matrix.single j i 1) = 0 := by
  ext a b
  have h : j ≠ Fin.castAdd r a := by intro h; have := congrArg Fin.val h; simp at this; omega
  simp [cut, h]

end
end Math.ExteriorSquareBlock
