import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkReducedAction

/-! The two unprojected literal color contractions times the first Weyl
pairing. Their orbit columns are outputs of the generator recipe, not an
independently supplied matrix. -/
namespace Physics.HeeckLeSixQuarkRecipe
noncomputable section
open LiSixQuarkLocalAction LiSixQuarkReducedAction
variable {K L : Type*} [Field K] [Field L]

def rawColor (k : Fin 2) : Vec (K := K) := match k with
  | 0 => ![-1,0,0,-1,1]
  | 1 => ![-1,0,-1,0,1]
def rawSpin : Vec (K := K) := ![1,0,0,0,0]
def seed (k : Fin 2) : Arr (K := K) := fun p q => rawColor k p*rawSpin q

def selectedSeed : Fin 25 → Fin 2 :=
  ![0,1,0,0,0,1,1,1,1,0,0,0,0,0,1,1,1,1,1,0,0,0,0,1,1]
def selectedWord : Fin 25 → List (Fin 4) :=
  ![[],[],[0],[2],[3],[0],[1],[2],[3],[0,2],[0,3],[2,1],[2,3],[3,2],
    [0,2],[1,2],[2,1],[2,3],[3,2],[0,2,3],[0,3,2],[2,1,3],[3,2,1],[0,2,1],[1,2,1]]

def orbit (j : Fin 25) : Arr (K := K) :=
  (selectedWord j).foldl (fun c g => action g c) (seed (selectedSeed j))

theorem map_color (σ : K →+* L) (k : Fin 2) :
    (fun p => σ (rawColor k p)) = rawColor k := by
  ext p
  fin_cases k <;> fin_cases p <;> simp [rawColor]
theorem map_spin (σ : K →+* L) : (fun p => σ (rawSpin p)) = rawSpin := by
  ext p
  fin_cases p <;> simp [rawSpin]

theorem map_seed (σ : K →+* L) (k : Fin 2) :
    LiSixQuarkSeedRecipe.mapArray σ (seed k) = seed k := by
  ext p q
  change σ (rawColor k p*rawSpin q) = rawColor k p*rawSpin q
  rw [map_mul, congrFun (map_color σ k) p, congrFun (map_spin σ) q]

theorem map_orbit (σ : K →+* L) (j : Fin 25) :
    LiSixQuarkSeedRecipe.mapArray σ (orbit j) = orbit j := by
  unfold orbit
  rw [← LiSixQuarkSeedRecipe.map_word, map_seed]

section Reduced
variable [CharZero K]

def reducedSeed (k : Fin 2) : Arr (K := K) := fun p q =>
  colorExtract (rawColor k) p*spinExtract rawSpin q
def reducedOrbit (j : Fin 25) : Arr (K := K) :=
  (selectedWord j).foldl (fun c g => reducedAction g c) (reducedSeed (selectedSeed j))

theorem extraction_seed (k : Fin 2) : extraction (seed (K := K) k) = reducedSeed k := by
  change row extractSpin (column extractColor (fun p q => rawColor k p*rawSpin q)) = _
  rw [column_outer, row_outer]
  rfl

theorem extraction_orbit (j : Fin 25) : extraction (orbit (K := K) j) = reducedOrbit j := by
  unfold orbit reducedOrbit
  rw [extraction_word, extraction_seed]

end Reduced
end
end Physics.HeeckLeSixQuarkRecipe
