import Physics.StandardModel.Operators.LiSixQuarkSeedRecipe

/-! The generator action after the explicit 2+3 splitting. The first two
coordinates and last three coordinates never mix. Every formula is an
identity on arbitrary vectors over an exact field. -/
namespace GUT.LiSixQuarkReducedAction
noncomputable section
open LiSixQuarkLocalAction LiSixQuarkYoungOperators
variable {K : Type*} [Field K] [CharZero K]

def colorExtract (x : Vec (K := K)) : Vec (K := K) :=
  ![x 1/2,x 2/2,x 0+(x 1-x 2)/2,x 3+x 1/2,x 4+x 2/2]
def spinExtract (x : Vec (K := K)) : Vec (K := K) :=
  ![(2*x 0+2*x 2-x 1-x 3-x 4)/6,
    (x 0+x 2+x 1+x 3-2*x 4)/6,
    (x 0-x 2+x 4)/2,(x 1-x 3+x 4)/2,x 4]

def colorAssemble (x : Vec (K := K)) : Vec (K := K) :=
  ![-x 0+x 1+x 2,2*x 0,2*x 1,-x 0+x 3,-x 1+x 4]
def spinAssemble (x : Vec (K := K)) : Vec (K := K) :=
  ![x 0+x 1+x 2,-x 0+2*x 1+x 3,x 0+x 1-x 2+x 4,
    -x 0+2*x 1-x 3+x 4,x 4]

theorem color_left_inverse (x : Vec (K := K)) : colorAssemble (colorExtract x) = x := by
  ext i; fin_cases i <;> simp [colorExtract, colorAssemble] <;> ring
theorem spin_left_inverse (x : Vec (K := K)) : spinAssemble (spinExtract x) = x := by
  ext i; fin_cases i <;> simp [spinExtract, spinAssemble] <;> ring

theorem color_injective : Function.Injective (colorExtract (K := K)) :=
  Function.LeftInverse.injective color_left_inverse
theorem spin_injective : Function.Injective (spinExtract (K := K)) :=
  Function.LeftInverse.injective spin_left_inverse

def colorReduced (g : Fin 4) (x : Vec (K := K)) : Vec (K := K) := match g with
  | 0 => ![x 0,x 1,-x 2,-x 3,-x 4]
  | 1 => ![-x 0-x 1,x 1,-x 3,-x 2,-x 4]
  | 2 => ![x 1,x 0,-x 2,x 4,x 3]
  | 3 => ![-x 0-x 1,x 1,-x 2-x 4,-x 3-x 4,x 4]
def spinReduced (g : Fin 4) (x : Vec (K := K)) : Vec (K := K) := match g with
  | 0 => ![-x 0,-x 1,x 2,x 3,x 4]
  | 1 => ![-x 0,-x 0+x 1,x 2+x 3-x 4,x 3,2*x 3-x 4]
  | 2 => ![x 1,x 0,x 2,x 2-x 3,x 4]
  | 3 => ![-x 0,-x 0+x 1,-x 2+x 3+x 4,x 3,x 4]

def extractColor : Vec (K := K) →ₗ[K] Vec (K := K) where
  toFun := colorExtract
  map_add' x y := by ext i; fin_cases i <;> simp [colorExtract] <;> ring
  map_smul' z x := by ext i; fin_cases i <;> simp [colorExtract] <;> ring

def extractSpin : Vec (K := K) →ₗ[K] Vec (K := K) where
  toFun := spinExtract
  map_add' x y := by ext i; fin_cases i <;> simp [spinExtract] <;> ring
  map_smul' z x := by ext i; fin_cases i <;> simp [spinExtract] <;> ring

def reducedColor (g : Fin 4) : Vec (K := K) →ₗ[K] Vec (K := K) where
  toFun := colorReduced g
  map_add' x y := by ext i; fin_cases g <;> fin_cases i <;> simp [colorReduced] <;> ring
  map_smul' z x := by ext i; fin_cases g <;> fin_cases i <;> simp [colorReduced] <;> ring

def reducedSpin (g : Fin 4) : Vec (K := K) →ₗ[K] Vec (K := K) where
  toFun := spinReduced g
  map_add' x y := by ext i; fin_cases g <;> fin_cases i <;> simp [spinReduced] <;> ring
  map_smul' z x := by ext i; fin_cases g <;> fin_cases i <;> simp [spinReduced] <;> ring

def extraction : Arr (K := K) →ₗ[K] Arr (K := K) :=
  (row extractSpin).comp (column extractColor)
def reducedAction (g : Fin 4) : Module.End K (Arr (K := K)) :=
  (row (reducedSpin g)).comp (column (reducedColor g))

theorem extraction_injective : Function.Injective (extraction (K := K)) := by
  intro c d h
  have hs (p : Fin 5) :
      (fun q => colorExtract (fun i => c i q) p) =
        (fun q => colorExtract (fun i => d i q) p) :=
    spin_injective (congrFun h p)
  ext p q
  exact congrFun (color_injective (funext (fun i => congrFun (hs i) q))) p

omit [CharZero K] in
@[simp] theorem reducedAction_apply (g : Fin 4) (c : Arr (K := K)) (p q : Fin 5) :
    reducedAction g c p q = spinReduced g (fun j => colorReduced g (fun i => c i j) p) q := rfl

theorem color_intertwine (g : Fin 4) (x : Vec (K := K)) :
    colorExtract (color g x) = colorReduced g (colorExtract x) := by
  ext i
  fin_cases g <;> fin_cases i <;> simp [colorExtract, color, colorReduced] <;> ring

theorem spin_intertwine (g : Fin 4) (x : Vec (K := K)) :
    spinExtract (spin g x) = spinReduced g (spinExtract x) := by
  ext i
  fin_cases g <;> fin_cases i <;> simp [spinExtract, spin, spinReduced] <;> ring

omit [CharZero K] in
/-- Row operations commute with column operations, by linearity alone. -/
theorem row_column_commute (S C : Vec (K := K) →ₗ[K] Vec (K := K))
    (c : Arr (K := K)) : row S (column C c) = column C (row S c) := by
  -- Expansion in the five coordinate vectors proves this uniformly in C,S,c.
  have expand (x : Vec (K := K)) : x = ∑ i : Fin 5, x i • Pi.single i 1 := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hc (x : Vec (K := K)) (p : Fin 5) :
      C x p = ∑ i : Fin 5, x i * C (Pi.single i 1) p := by
    conv_lhs => rw [expand x]
    simp [map_sum, map_smul, Finset.sum_apply, smul_eq_mul]
  ext p q
  change S (fun j => C (fun i => c i j) p) q = C (fun i => S (c i) q) p
  have hl : (fun j => C (fun i => c i j) p) =
      (fun j => ∑ i : Fin 5, c i j * C (Pi.single i 1) p) :=
    funext (fun j => hc (fun i => c i j) p)
  rw [hl]
  conv_rhs => rw [hc]
  have he : (fun j => ∑ i : Fin 5, c i j * C (Pi.single i 1) p) =
      ∑ i : Fin 5, C (Pi.single i 1) p • c i := by
    ext j
    simp [Finset.sum_apply, smul_eq_mul, mul_comm]
  rw [he]
  simp [map_sum, map_smul, Finset.sum_apply, smul_eq_mul, mul_comm]

theorem extraction_action (g : Fin 4) (c : Arr (K := K)) :
    extraction (action g c) = reducedAction g (extraction c) := by
  change row extractSpin (column extractColor
    (row (spinLinear g) (column (colorLinear g) c))) =
    row (reducedSpin g) (column (reducedColor g)
      (row extractSpin (column extractColor c)))
  rw [← row_column_commute, ← row_column_commute]
  have hc : column extractColor (column (colorLinear g) c) =
      column (reducedColor g) (column extractColor c) := by
    ext p q; exact congrFun (color_intertwine g (fun i => c i q)) p
  rw [hc]
  ext p q
  exact congrFun (spin_intertwine g _) q

theorem extraction_young (k : Fin 11) (c : Arr (K := K)) :
    extraction (young action k c) = young reducedAction k (extraction c) :=
  map_young extraction action reducedAction extraction_action k c

theorem extraction_word (w : List (Fin 4)) (c : Arr (K := K)) :
    extraction (w.foldl (fun c g => action g c) c) =
      w.foldl (fun c g => reducedAction g c) (extraction c) := by
  induction w generalizing c with
  | nil => rfl
  | cons g w ih =>
    change extraction (w.foldl (fun c g => action g c) (action g c)) = _
    rw [ih, extraction_action]
    rfl

end
end GUT.LiSixQuarkReducedAction
