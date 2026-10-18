import Physics.StandardModel.Operators.HeeckLeSixQuarkData
import Physics.StandardModel.Operators.LiSixQuarkLocalBasis

/-! Two literal Heeck–Le u²d⁴ contractions, Section 9.4 of 2604.25134v2.
U,D,U,D,D,D order: color triples (134)(025) and (124)(035).
Two fermion exchanges and two epsilon reversals give net sign +1. -/
namespace GUT.HeeckLeSixQuarkCertificate
set_option autoImplicit false
noncomputable section
open SMEpsilonTensor SixQuarkInvariant SixQuarkSpeciesQuotient

def seedCoordinates (k : Fin 2) : Fin 5 → Fin 5 → ℂ :=
  fun p q => (rationalSeedCoordinates k p q : ℂ)

def seed (k : Fin 2) : Coefficient := reconstruct (seedCoordinates k)

def paperColor (k : Fin 2) (v : Fin 6 → Color) : ℂ :=
  if k = 0 then eps3 (v 1) (v 3) (v 4) * eps3 (v 0) (v 2) (v 5)
  else eps3 (v 1) (v 2) (v 4) * eps3 (v 0) (v 3) (v 5)

theorem color_identity (k : Fin 2) (v : Fin 6 → Color) :
    paperColor k v = ∑ p, seedCoordinates k p 0 * SixColorInvariant.pairingValue p v := by
  fin_cases k <;>
    simp [paperColor, seedCoordinates, rationalSeedCoordinates,
      HeeckLeSixQuarkRecipe.seed, HeeckLeSixQuarkRecipe.rawColor,
      HeeckLeSixQuarkRecipe.rawSpin, Fin.sum_univ_succ, SixColorInvariant.pairingValue, eps3] <;> ring

theorem seed_spin_zero (k : Fin 2) (p q : Fin 5) (hq : q ≠ 0) :
    seedCoordinates k p q = 0 := by
  fin_cases k <;> fin_cases p <;> fin_cases q <;>
    norm_num [seedCoordinates, rationalSeedCoordinates, HeeckLeSixQuarkRecipe.seed,
      HeeckLeSixQuarkRecipe.rawColor, HeeckLeSixQuarkRecipe.rawSpin] at *

theorem literal (k : Fin 2) (v : Fin 6 → Color) (s : Fin 6 → Spin) :
    seed k (fun i => v i ⊗ₜ[ℂ] s i) =
      paperColor k v * (eps2 (s 0) (s 1) * eps2 (s 2) (s 3) * eps2 (s 4) (s 5)) := by
  rw [seed, reconstruct_apply, color_identity]
  simp only [Fin.sum_univ_succ]
  simp [seed_spin_zero, SixWeylMultilinear.pairingValue,
    SixWeylInvariant.pairingValue]
  ring

def orbitArray (j : Fin 25) : Fin 5 → Fin 5 → ℂ :=
  (selectedWord j).foldl (fun c g => transform c g) (seedCoordinates (selectedSeed j))

def orbitCoefficient (j : Fin 25) : Coefficient :=
  LiSixQuarkLocalBasis.wordCoefficient (selectedWord j) (seed (selectedSeed j))

theorem orbitCoefficient_eq (j : Fin 25) :
    orbitCoefficient j = reconstruct (orbitArray j) := by
  exact LiSixQuarkLocalBasis.word_reconstruct _ _

end
end GUT.HeeckLeSixQuarkCertificate
