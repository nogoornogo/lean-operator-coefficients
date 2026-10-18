import Physics.StandardModel.Operators.LiSixQuarkBlockSolvers
import Physics.StandardModel.Operators.LiSixQuarkBlockCoordinates
import Physics.StandardModel.Operators.LiSixQuarkFiniteData
import Physics.StandardModel.Operators.LiSixQuarkSeedDirections

/-! The selected columns in product-block coordinates. Couplings are explicit:
triples are separated by sums/differences, and the 2-by-2 block is resolved by
trace, alternating and standard components. -/
namespace GUT.LiSixQuarkBlockAssembly
noncomputable section
open LiSixQuarkBlockSolvers LiSixQuarkCertificate LiSixQuarkPairBlock
open scoped BigOperators
abbrev Array := Fin 5 → Fin 5 → ℂ

/-- Color extraction applied columnwise, using the 2+3 formulas. -/
def colorEntries (c : Array) : Array :=
  ![(fun q => c 1 q/2), (fun q => c 2 q/2),
    (fun q => c 0 q+(c 1 q-c 2 q)/2),
    (fun q => c 3 q+c 1 q/2), (fun q => c 4 q+c 2 q/2)]
/-- Spin extraction applied rowwise. -/
def entries (c : Array) (p : Fin 5) : Fin 5 → ℂ :=
  let x := colorEntries c p
  ![(2*x 0+2*x 2-x 1-x 3-x 4)/6,
    (x 0+x 2+x 1+x 3-2*x 4)/6,
    (x 0-x 2+x 4)/2, (x 1-x 3+x 4)/2, x 4]

def a32 (v : Fin 25 → ℂ) : Fin 3 → ℂ := ![v 0,v 1,v 2]
def d32 (v : Fin 25 → ℂ) : Fin 3 → ℂ := ![v 6-v 9,v 7-v 10,v 8-v 11]
def a23 (v : Fin 25 → ℂ) : Fin 3 → ℂ := ![v 3+v 0/2,v 4+v 1/2,v 5+v 2/2]
def s23 (v : Fin 25 → ℂ) : Fin 3 → ℂ := ![v 6+v 9,v 7+v 10,v 8+v 11]
def h33 (v : Fin 25 → ℂ) : Fin 3 → ℂ := ![v 14,v 15,v 16]
def s33 (v : Fin 25 → ℂ) : Fin 2 → ℂ := ![v 19,v 20]
def l33 (v : Fin 25 → ℂ) : Fin 3 → ℂ := ![v 21,v 22,v 23]

def y22 (v : Fin 25 → ℂ) : Fin 4 → ℂ :=
  let t := v 24
  let r := v 12+v 13
  let u := v 17+2*v 19
  let w := v 18+2*v 20
  ![t+r-u/3+w/3, 2*r+u/3+2*w/3, -2*r+2*u/3+w/3, t-r+u/3-w/3]
def y23 (v : Fin 25 → ℂ) := forward23 (a23 v) (s23 v)
def y32 (v : Fin 25 → ℂ) := forward32 (a32 v) (d32 v)
def y33 (v : Fin 25 → ℂ) := forward33 (v 12-v 13) (h33 v) (s33 v) (l33 v)

def presentation (v : Fin 25 → ℂ) : Array :=
  ![![y22 v 0,y22 v 1,y23 v 0,y23 v 1,y23 v 2],
    ![y22 v 2,y22 v 3,y23 v 3,y23 v 4,y23 v 5],
    ![y32 v 0,y32 v 1,y33 v 0,y33 v 1,y33 v 2],
    ![y32 v 2,y32 v 3,y33 v 3,y33 v 4,y33 v 5],
    ![y32 v 4,y32 v 5,y33 v 6,y33 v 7,y33 v 8]]

/-- Assembly in the existing independently identified local coordinates. -/
def originalAssembly (v : Fin 25 → ℂ) : Array := fun p q =>
  ∑ j : Fin 25, (basisRational ((finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25) (p,q)) j : ℂ) * v j

/-- The displayed five-coordinate extraction is the symbolic tensor map. -/
theorem entries_eq_extraction (c : Array) :
    entries c = LiSixQuarkReducedAction.extraction c := by
  ext p q
  fin_cases p <;> fin_cases q <;> rfl

def reducedOrbit (j : Fin 25) : Array :=
  (selectedWord j).foldl (fun c g => LiSixQuarkReducedAction.reducedAction g c)
    (LiSixQuarkReducedSeeds.reducedSeed (selectedSeed j))

theorem originalAssembly_sum (v : Fin 25 → ℂ) :
    originalAssembly v = ∑ j : Fin 25, v j • (fun p q => (orbitR j p q : ℂ)) := by
  ext p q
  simp only [originalAssembly, basisRational, Equiv.symm_apply_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem orbit_cast (j : Fin 25) : (fun p q => (orbitR j p q : ℂ)) =
    (selectedWord j).foldl (fun c g => LiSixQuarkLocalAction.action g c)
      (LiSixQuarkSeedRecipe.projected (selectedSeed j)) := by
  change LiSixQuarkSeedRecipe.mapArray (Rat.castHom ℂ)
    ((selectedWord j).foldl (fun c g => LiSixQuarkLocalAction.action g c)
      (LiSixQuarkSeedRecipe.projected (K := ℚ) (selectedSeed j))) = _
  rw [← LiSixQuarkSeedRecipe.map_word, LiSixQuarkSeedRecipe.map_projected]

theorem entries_orbit (j : Fin 25) :
    entries (fun p q => (orbitR j p q : ℂ)) = reducedOrbit j := by
  rw [entries_eq_extraction, orbit_cast, LiSixQuarkReducedAction.extraction_word,
    LiSixQuarkReducedSeeds.extraction_projected]
  rfl

/-- All remaining assembly algebra takes place inside the small blocks. -/
theorem entries_original (v : Fin 25 → ℂ) :
    entries (originalAssembly v) = ∑ j : Fin 25, v j • reducedOrbit j := by
  rw [entries_eq_extraction, originalAssembly_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  rw [← entries_eq_extraction, entries_orbit]

theorem presentation_entry00 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 0 0 = presentation v 0 0 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_entry01 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 0 1 = presentation v 0 1 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_entry02 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 0 2 = presentation v 0 2 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_entry03 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 0 3 = presentation v 0 3 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_entry04 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 0 4 = presentation v 0 4 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_row0 (v : Fin 25 → ℂ) (q : Fin 5) :
    entries (originalAssembly v) 0 q = presentation v 0 q := by
  fin_cases q
  · exact presentation_entry00 v
  · exact presentation_entry01 v
  · exact presentation_entry02 v
  · exact presentation_entry03 v
  · exact presentation_entry04 v

theorem presentation_entry10 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 1 0 = presentation v 1 0 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_entry11 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 1 1 = presentation v 1 1 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_entry12 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 1 2 = presentation v 1 2 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_entry13 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 1 3 = presentation v 1 3 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_entry14 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 1 4 = presentation v 1 4 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_row1 (v : Fin 25 → ℂ) (q : Fin 5) :
    entries (originalAssembly v) 1 q = presentation v 1 q := by
  fin_cases q
  · exact presentation_entry10 v
  · exact presentation_entry11 v
  · exact presentation_entry12 v
  · exact presentation_entry13 v
  · exact presentation_entry14 v

theorem presentation_entry20 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 2 0 = presentation v 2 0 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_entry21 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 2 1 = presentation v 2 1 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_entry22 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 2 2 = presentation v 2 2 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_entry23 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 2 3 = presentation v 2 3 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_entry24 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 2 4 = presentation v 2 4 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_row2 (v : Fin 25 → ℂ) (q : Fin 5) :
    entries (originalAssembly v) 2 q = presentation v 2 q := by
  fin_cases q
  · exact presentation_entry20 v
  · exact presentation_entry21 v
  · exact presentation_entry22 v
  · exact presentation_entry23 v
  · exact presentation_entry24 v

theorem presentation_entry30 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 3 0 = presentation v 3 0 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_entry31 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 3 1 = presentation v 3 1 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_entry32 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 3 2 = presentation v 3 2 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_entry33 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 3 3 = presentation v 3 3 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_entry34 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 3 4 = presentation v 3 4 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_row3 (v : Fin 25 → ℂ) (q : Fin 5) :
    entries (originalAssembly v) 3 q = presentation v 3 q := by
  fin_cases q
  · exact presentation_entry30 v
  · exact presentation_entry31 v
  · exact presentation_entry32 v
  · exact presentation_entry33 v
  · exact presentation_entry34 v

theorem presentation_entry40 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 4 0 = presentation v 4 0 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_entry41 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 4 1 = presentation v 4 1 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_entry42 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 4 2 = presentation v 4 2 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_entry43 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 4 3 = presentation v 4 3 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_entry44 (v : Fin 25 → ℂ) :
    entries (originalAssembly v) 4 4 = presentation v 4 4 := by
  rw [entries_original]
  simp_rw [reducedOrbit, LiSixQuarkSeedDirections.reducedSeed_direction]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selectedWord, selectedSeed, LiSixQuarkSeedDirections.seedDirection,
    LiSixQuarkSeedDirections.direction0, LiSixQuarkSeedDirections.direction2,
    LiSixQuarkSeedDirections.direction4, LiSixQuarkSeedDirections.direction6,
    LiSixQuarkSeedDirections.direction7, LiSixQuarkSeedDirections.direction9,
    LiSixQuarkSeedDirections.direction10, LiSixQuarkReducedAction.reducedAction_apply,
    LiSixQuarkReducedAction.colorReduced, LiSixQuarkReducedAction.spinReduced,
    presentation, y22, y23, y32, y33, a32, d32, a23, s23, h33, s33, l33,
    forward23, forward32, forward33, Fin.sum_univ_succ]
  all_goals ring

theorem presentation_row4 (v : Fin 25 → ℂ) (q : Fin 5) :
    entries (originalAssembly v) 4 q = presentation v 4 q := by
  fin_cases q
  · exact presentation_entry40 v
  · exact presentation_entry41 v
  · exact presentation_entry42 v
  · exact presentation_entry43 v
  · exact presentation_entry44 v

theorem presentation_correct (v : Fin 25 → ℂ) :
    entries (originalAssembly v) = presentation v := by
  ext p q
  fin_cases p
  · exact presentation_row0 v q
  · exact presentation_row1 v q
  · exact presentation_row2 v q
  · exact presentation_row3 v q
  · exact presentation_row4 v q

end
end GUT.LiSixQuarkBlockAssembly
