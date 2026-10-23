import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkSpeciesQuotient

/-! Small component formulas for the actual generators. Each color/spin map
uses five inputs; tensor transport is composed from these maps, never expanded
as an unnamed 25-by-25 array. The formulas work over both Q and C. -/
namespace Physics.LiSixQuarkLocalAction
noncomputable section
variable {K : Type*} [Field K]
abbrev Vec := Fin 5 → K
abbrev Arr := Fin 5 → Fin 5 → K

def color (g : Fin 4) (x : Vec (K := K)) : Vec (K := K) := match g with
  | 0 => ![-x 0-x 1+x 2,x 1,x 2,-x 1-x 3,-x 2-x 4]
  | 1 => ![x 2-x 3,-x 1-x 2,x 2,-x 0+x 2,-x 2-x 4]
  | 2 => ![-x 0,x 2,x 1,x 4,x 3]
  | 3 => ![-x 0+x 2-x 4,-x 1-x 2,x 2,-x 3-x 4,x 4]

def spin (g : Fin 4) (x : Vec (K := K)) : Vec (K := K) := match g with
  | 0 => ![-x 2+x 4,-x 3+x 4,-x 0+x 4,-x 1+x 4,x 4]
  | 1 => ![x 1-x 2,x 1,-x 0+x 1,x 1-x 4,x 1-x 3]
  | 2 => ![x 0,x 0-x 1,x 2,x 2-x 3+x 4,x 4]
  | 3 => ![-x 0+x 1+x 4,x 1,-x 2+x 3,x 3,x 4]

def colorLinear (g : Fin 4) : Vec (K := K) →ₗ[K] Vec (K := K) where
  toFun := color g
  map_add' x y := by
    ext i; fin_cases g <;> fin_cases i <;> simp [color] <;> ring
  map_smul' z x := by
    ext i; fin_cases g <;> fin_cases i <;> simp [color] <;> ring

def spinLinear (g : Fin 4) : Vec (K := K) →ₗ[K] Vec (K := K) where
  toFun := spin g
  map_add' x y := by
    ext i; fin_cases g <;> fin_cases i <;> simp [spin] <;> ring
  map_smul' z x := by
    ext i; fin_cases g <;> fin_cases i <;> simp [spin] <;> ring

def column (L : Vec (K := K) →ₗ[K] Vec (K := K)) : Arr (K := K) →ₗ[K] Arr (K := K) where
  toFun c p q := L (fun i => c i q) p
  map_add' c d := by
    ext p q
    exact congrFun (L.map_add (fun i => c i q) (fun i => d i q)) p
  map_smul' z c := by
    ext p q
    exact congrFun (L.map_smul z (fun i => c i q)) p

def row (L : Vec (K := K) →ₗ[K] Vec (K := K)) : Arr (K := K) →ₗ[K] Arr (K := K) where
  toFun c p := L (c p)
  map_add' c d := by ext p q; exact congrFun (L.map_add (c p) (d p)) q
  map_smul' z c := by ext p q; exact congrFun (L.map_smul z (c p)) q

def action (g : Fin 4) : Module.End K (Arr (K := K)) :=
  (row (spinLinear g)).comp (column (colorLinear g))

/-- Column and row transport preserve separated tensors. -/
theorem column_outer (L : Vec (K := K) →ₗ[K] Vec (K := K)) (a b : Vec (K := K)) :
    column L (fun p q => a p*b q) = fun p q => L a p*b q := by
  ext p q
  have h : (fun i => a i*b q) = b q • a := by ext i; simp [mul_comm]
  change L (fun i => a i*b q) p = _
  rw [h, L.map_smul]
  simp [mul_comm]

theorem row_outer (L : Vec (K := K) →ₗ[K] Vec (K := K)) (a b : Vec (K := K)) :
    row L (fun p q => a p*b q) = fun p q => a p*L b q := by
  ext p q
  change L (a p • b) q = _
  rw [L.map_smul]
  rfl

open Matrix SixQuarkSpeciesQuotient

theorem color_actual (g : Fin 4) (x : Fin 5 → ℂ) : color g x = colorMatrix g *ᵥ x := by
  ext i
  fin_cases g <;> fin_cases i <;>
    simp [color, colorMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem spin_actual (g : Fin 4) (x : Fin 5 → ℂ) : spin g x = spinMatrix g *ᵥ x := by
  ext i
  fin_cases g <;> fin_cases i <;>
    simp [spin, spinMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- Actual generator transport is a uniform linear identity, not a check of
an evaluated invariant-space matrix. -/
theorem action_actual (g : Fin 4) (c : Arr (K := ℂ)) : action g c = transform c g := by
  ext p q
  change spin g (fun j => color g (fun i => c i j) p) q = _
  rw [spin_actual]
  simp_rw [color_actual]
  simp only [Matrix.mulVec, dotProduct, transform, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end Physics.LiSixQuarkLocalAction
