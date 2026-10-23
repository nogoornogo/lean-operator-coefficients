import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkOrbitRecipe
import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkYoungData

/-! Compatibility names for the literal source dictionary and its exact
Young-action recipe. Projected seed coordinates and forward columns are
outputs of that recipe; no cached seed, dense inverse or rank table is input. -/
namespace Physics.LiSixQuarkConvention
noncomputable section
abbrev permutationData := LiSixQuarkYoungData.permutationData
abbrev seedColorData := LiSixQuarkYoungData.seedColorData
abbrev youngWeights := LiSixQuarkYoungData.youngWeights
abbrev normalization := LiSixQuarkYoungData.normalization

def rationalSeedCoordinates (k : Fin 11) : Fin 5 → Fin 5 → ℚ :=
  LiSixQuarkSeedRecipe.projected k

def seedCoordinates (k : Fin 11) (p q : Fin 5) : ℂ := rationalSeedCoordinates k p q

def basisEntry {n : ℕ} (i j : Fin n) : ℚ := if i = j then 1 else 0
def colorEpsilon (a b c : Fin 3) : ℚ :=
  basisEntry a 0 * basisEntry b 1 * basisEntry c 2 +
  basisEntry a 1 * basisEntry b 2 * basisEntry c 0 +
  basisEntry a 2 * basisEntry b 0 * basisEntry c 1 -
  basisEntry a 0 * basisEntry b 2 * basisEntry c 1 -
  basisEntry a 1 * basisEntry b 0 * basisEntry c 2 -
  basisEntry a 2 * basisEntry b 1 * basisEntry c 0
def spinEpsilon (a b : Fin 2) : ℚ :=
  basisEntry a 0 * basisEntry b 1 - basisEntry a 1 * basisEntry b 0

def rationalValue (k : Fin 11) (v : Fin 6 → Fin 3) (s : Fin 6 → Fin 2) : ℚ :=
  ∑ g : Fin 48, youngWeights k g / normalization k *
    (let q : Fin 6 → Fin 6 := fun i =>
      (![1,3,4,5,0,2] : Fin 6 → Fin 6) (permutationData g i)
     let t := seedColorData k
     colorEpsilon (v (q (t 0))) (v (q (t 1))) (v (q (t 2))) *
       colorEpsilon (v (q (t 3))) (v (q (t 4))) (v (q (t 5))) *
       (spinEpsilon (s (q 0)) (s (q 3)) *
         spinEpsilon (s (q 4)) (s (q 1)) * spinEpsilon (s (q 5)) (s (q 2))))

end
end Physics.LiSixQuarkConvention
