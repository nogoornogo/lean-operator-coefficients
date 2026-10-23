import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkSeedRecipe

/-! Selected sources and short exchange words define the forward columns.
No forward/inverse matrix or projected seed table is supplied as input. -/
namespace Physics.LiSixQuarkCertificate
noncomputable section
def selectedSeed : Fin 25 → Fin 11 := ![0,0,0,1,1,1,2,2,2,3,3,3,4,5,6,6,6,7,7,8,8,9,9,9,10]
def selectedWord : Fin 25 → List (Fin 4) := ![[],[3],[3,2],[],[3],[3,2],[],[2],[2,3],[],[2],[2,3],[],[],[],[3],[3,2],[],[2],[],[2],[],[2],[2,3],[]]

def colorMatrixR : Fin 4 → Matrix (Fin 5) (Fin 5) ℚ := ![
  !![-1,-1,1,0,0; 0,1,0,0,0; 0,0,1,0,0; 0,-1,0,-1,0; 0,0,-1,0,-1],
  !![0,0,1,-1,0; 0,-1,-1,0,0; 0,0,1,0,0; -1,0,1,0,0; 0,0,-1,0,-1],
  !![-1,0,0,0,0; 0,0,1,0,0; 0,1,0,0,0; 0,0,0,0,1; 0,0,0,1,0],
  !![-1,0,1,0,-1; 0,-1,-1,0,0; 0,0,1,0,0; 0,0,0,-1,-1; 0,0,0,0,1]]
def spinMatrixR : Fin 4 → Matrix (Fin 5) (Fin 5) ℚ := ![
  !![0,0,-1,0,1; 0,0,0,-1,1; -1,0,0,0,1; 0,-1,0,0,1; 0,0,0,0,1],
  !![0,1,-1,0,0; 0,1,0,0,0; -1,1,0,0,0; 0,1,0,0,-1; 0,1,0,-1,0],
  !![1,0,0,0,0; 1,-1,0,0,0; 0,0,1,0,0; 0,0,1,-1,1; 0,0,0,0,1],
  !![-1,1,0,0,1; 0,1,0,0,0; 0,0,-1,1,0; 0,0,0,1,0; 0,0,0,0,1]]

def transformR (c : Fin 5 → Fin 5 → ℚ) (g : Fin 4) : Fin 5 → Fin 5 → ℚ :=
  LiSixQuarkLocalAction.action g c

def orbitR (j : Fin 25) : Fin 5 → Fin 5 → ℚ :=
  (selectedWord j).foldl transformR (LiSixQuarkSeedRecipe.projected (selectedSeed j))

/-- The matrix is an output presentation of the selected actual-source orbits. -/
def basisRational : Matrix (Fin 25) (Fin 25) ℚ := fun i j =>
  orbitR j ((finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25).symm i).1
    ((finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25).symm i).2

end
end Physics.LiSixQuarkCertificate
