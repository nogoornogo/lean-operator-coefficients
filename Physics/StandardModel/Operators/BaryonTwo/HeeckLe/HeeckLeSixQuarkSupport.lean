import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkBlocks

/-! The color complement stays a complement under every generator. Thus the
first source cannot contribute to either color-pair block, for any word. -/
namespace Physics.HeeckLeSixQuarkSupport
noncomputable section
open LiSixQuarkLocalAction LiSixQuarkReducedAction HeeckLeSixQuarkRecipe
variable {K : Type*} [Field K]

def PairZero (c : Arr (K := K)) : Prop := ∀ q, c 0 q = 0 ∧ c 1 q = 0

theorem color_pair_zero (g : Fin 4) (x : Vec (K := K)) (h0 : x 0 = 0) (h1 : x 1 = 0) :
    colorReduced g x 0 = 0 ∧ colorReduced g x 1 = 0 := by
  fin_cases g <;> simp [colorReduced, h0, h1]

theorem action_pair_zero (g : Fin 4) (c : Arr (K := K)) (h : PairZero c) :
    PairZero (reducedAction g c) := by
  have h0 : (fun j => colorReduced g (fun i => c i j) 0) = (0 : Vec (K := K)) := by
    ext j
    exact (color_pair_zero g (fun i => c i j) (h j).1 (h j).2).1
  have h1 : (fun j => colorReduced g (fun i => c i j) 1) = (0 : Vec (K := K)) := by
    ext j
    exact (color_pair_zero g (fun i => c i j) (h j).1 (h j).2).2
  intro q
  constructor
  · change (reducedSpin g) (fun j => colorReduced g (fun i => c i j) 0) q = 0
    rw [h0, map_zero]
    rfl
  · change (reducedSpin g) (fun j => colorReduced g (fun i => c i j) 1) q = 0
    rw [h1, map_zero]
    rfl

theorem word_pair_zero (w : List (Fin 4)) (c : Arr (K := K)) (h : PairZero c) :
    PairZero (w.foldl (fun c g => reducedAction g c) c) := by
  induction w generalizing c with
  | nil => exact h
  | cons g w ih => exact ih _ (action_pair_zero g c h)

theorem source0_pair_zero : PairZero (HeeckLeSixQuarkBlocks.source (K := K) 0) :=
  HeeckLeSixQuarkBlocks.source0_pair_zero

theorem orbit_source0_pair_zero (j : Fin 25) (h : selectedSeed j = 0) :
    PairZero (HeeckLeSixQuarkBlocks.orbit (K := K) j) := by
  unfold HeeckLeSixQuarkBlocks.orbit
  rw [h]
  exact word_pair_zero _ _ source0_pair_zero

end
end Physics.HeeckLeSixQuarkSupport
