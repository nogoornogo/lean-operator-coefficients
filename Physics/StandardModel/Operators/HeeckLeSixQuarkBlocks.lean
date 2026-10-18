import Physics.StandardModel.Operators.HeeckLeSixQuarkRecipe

/-! Integral coordinates for the two raw source orbits. Only the spin pair
and spin triple are rescaled (by 12 and 4); the physical source coefficients
are unchanged. This avoids repeatedly expanding rational source coordinates. -/
namespace GUT.HeeckLeSixQuarkBlocks
noncomputable section
open LiSixQuarkLocalAction LiSixQuarkReducedAction HeeckLeSixQuarkRecipe
variable {K : Type*} [Field K] [CharZero K]

def scaleSpin (x : Vec (K := K)) : Vec (K := K) :=
  ![12*x 0,12*x 1,4*x 2,4*x 3,4*x 4]
def scaleLinear : Vec (K := K) →ₗ[K] Vec (K := K) where
  toFun := scaleSpin
  map_add' x y := by ext i; fin_cases i <;> simp [scaleSpin] <;> ring
  map_smul' z x := by ext i; fin_cases i <;> simp [scaleSpin] <;> ring

def normalize : Arr (K := K) →ₗ[K] Arr (K := K) := row scaleLinear

def unscale (c : Arr (K := K)) : Arr (K := K) := fun p =>
  ![c p 0/12,c p 1/12,c p 2/4,c p 3/4,c p 4/4]

theorem unscale_normalize (c : Arr (K := K)) : unscale (normalize c) = c := by
  ext p q
  fin_cases q <;> simp [unscale, normalize, row, scaleLinear, scaleSpin]

omit [CharZero K] in
theorem spin_scale_commute (g : Fin 4) (x : Vec (K := K)) :
    scaleSpin (spinReduced g x) = spinReduced g (scaleSpin x) := by
  ext i
  fin_cases g <;> fin_cases i <;> simp [scaleSpin, spinReduced] <;> ring

omit [CharZero K] in
theorem normalize_action (g : Fin 4) (c : Arr (K := K)) :
    normalize (reducedAction g c) = reducedAction g (normalize c) := by
  change row scaleLinear (row (reducedSpin g) (column (reducedColor g) c)) =
    row (reducedSpin g) (column (reducedColor g) (row scaleLinear c))
  rw [← row_column_commute]
  ext p q
  exact congrFun (spin_scale_commute g _) q

omit [CharZero K] in
theorem normalize_word (w : List (Fin 4)) (c : Arr (K := K)) :
    normalize (w.foldl (fun c g => reducedAction g c) c) =
      w.foldl (fun c g => reducedAction g c) (normalize c) := by
  induction w generalizing c with
  | nil => rfl
  | cons g w ih =>
    change normalize (w.foldl (fun c g => reducedAction g c) (reducedAction g c)) = _
    rw [ih, normalize_action]
    rfl

def colorBase (k : Fin 2) : Vec (K := K) := match k with
  | 0 => ![0,0,-2,-2,2]
  | 1 => ![0,-1,-1,0,1]
def spinBase : Vec (K := K) := ![2,1,1,0,0]
def source (k : Fin 2) : Arr (K := K) := fun p q => colorBase k p*spinBase q

theorem color_amplitude (k : Fin 2) : colorBase (K := K) k = (2 : K) • colorExtract (rawColor k) := by
  ext p
  fin_cases k <;> fin_cases p <;> norm_num [colorBase, colorExtract, rawColor]

theorem spin_amplitude : scaleSpin (spinExtract (rawSpin (K := K))) = (2 : K) • spinBase := by
  ext q
  fin_cases q <;> norm_num [scaleSpin, spinExtract, rawSpin, spinBase]

theorem normalize_seed (k : Fin 2) : normalize (reducedSeed (K := K) k) = source k := by
  change row scaleLinear (fun p q => colorExtract (rawColor k) p*spinExtract rawSpin q) = _
  rw [row_outer]
  ext p q
  change colorExtract (rawColor k) p*scaleSpin (spinExtract rawSpin) q = _
  rw [spin_amplitude]
  change colorExtract (rawColor (K := K) k) p*((2 : K)*spinBase (K := K) q) =
    colorBase (K := K) k p*spinBase (K := K) q
  rw [color_amplitude]
  change _ = ((2 : K)*colorExtract (rawColor (K := K) k) p)*spinBase (K := K) q
  ring

def orbit (j : Fin 25) : Arr (K := K) :=
  (selectedWord j).foldl (fun c g => reducedAction g c) (source (selectedSeed j))

theorem normalize_orbit (j : Fin 25) : normalize (reducedOrbit (K := K) j) = orbit j := by
  unfold reducedOrbit orbit
  rw [normalize_word, normalize_seed]

omit [CharZero K] in
theorem source0_pair_zero (q : Fin 5) : source (K := K) 0 0 q = 0 ∧ source (K := K) 0 1 q = 0 := by
  simp [source, colorBase]

end
end GUT.HeeckLeSixQuarkBlocks
