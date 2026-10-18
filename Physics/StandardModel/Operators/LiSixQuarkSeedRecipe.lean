import Physics.StandardModel.Operators.LiSixQuarkSemanticSeeds

/-! An exact field-independent recipe: four color diagrams, one spin diagram,
then the named Young factors. This replaces cached projected seed values. -/
namespace GUT.LiSixQuarkSeedRecipe
noncomputable section
open LiSixQuarkLocalAction LiSixQuarkYoungOperators
variable {K L : Type*} [Field K] [Field L]

def rawColor (kind : Fin 4) : Fin 5 → K :=
  (![![0,0,1,0,0], ![1,-1,1,1,-1], ![0,1,0,0,0], ![-1,1,0,-1,0]] :
    Fin 4 → Fin 5 → K) kind
def rawSpin : Fin 5 → K := ![1,1,0,1,1]
def raw (k : Fin 11) : Arr (K := K) :=
  fun p q => rawColor (LiSixQuarkRawSource.colorKind k) p * rawSpin q
def projected (k : Fin 11) : Arr (K := K) := young action k (raw k)

def mapArray (σ : K →+* L) : Arr (K := K) →ₛₗ[σ] Arr (K := L) where
  toFun c p q := σ (c p q)
  map_add' c d := by ext p q; exact σ.map_add _ _
  map_smul' z c := by ext p q; exact σ.map_mul _ _

theorem map_color (σ : K →+* L) (g : Fin 4) (x : Vec (K := K)) :
    (fun p => σ (color g x p)) = color g (fun p => σ (x p)) := by
  ext p
  fin_cases g <;> fin_cases p <;> simp [color]
theorem map_spin (σ : K →+* L) (g : Fin 4) (x : Vec (K := K)) :
    (fun p => σ (spin g x p)) = spin g (fun p => σ (x p)) := by
  ext p
  fin_cases g <;> fin_cases p <;> simp [spin]

theorem map_action (σ : K →+* L) (g : Fin 4) (c : Arr (K := K)) :
    mapArray σ (action g c) = action g (mapArray σ c) := by
  ext p q
  change σ (spin g (fun j => color g (fun i => c i j) p) q) = _
  have hs := congrFun (map_spin σ g (fun j => color g (fun i => c i j) p)) q
  rw [hs]
  change spin g (fun j => σ (color g (fun i => c i j) p)) q = _
  simp_rw [show ∀ j, σ (color g (fun i => c i j) p) =
    color g (fun i => σ (c i j)) p from fun j => congrFun (map_color σ g _) p]
  rfl

theorem map_raw (σ : K →+* L) (k : Fin 11) : mapArray σ (raw k) = raw k := by
  ext p q
  change σ (rawColor _ p * rawSpin q) = _
  simp only [map_mul]
  congr 1
  · generalize LiSixQuarkRawSource.colorKind k = kind
    fin_cases kind <;> fin_cases p <;> simp [rawColor]
  · fin_cases q <;> simp [rawSpin]

theorem map_projected (σ : K →+* L) (k : Fin 11) :
    mapArray σ (projected k) = projected k := by
  unfold projected
  rw [map_young_semilinear (mapArray σ) action action (map_action σ), map_raw]

theorem map_word (σ : K →+* L) (w : List (Fin 4)) (c : Arr (K := K)) :
    w.foldl (fun c g => action g c) (mapArray σ c) =
      mapArray σ (w.foldl (fun c g => action g c) c) := by
  induction w generalizing c with
  | nil => rfl
  | cons g w ih =>
    change w.foldl (fun c g => action g c) (action g (mapArray σ c)) = _
    rw [← map_action]
    exact ih _

theorem complex_raw (k : Fin 11) : raw (K := ℂ) k = LiSixQuarkRawSource.rawCoordinates k := rfl
theorem complex_projected (k : Fin 11) :
    projected (K := ℂ) k = LiSixQuarkSemanticSeeds.seedCoordinates k := rfl

theorem rational_cast (k : Fin 11) :
    (fun p q => (projected (K := ℚ) k p q : ℂ)) =
      LiSixQuarkSemanticSeeds.seedCoordinates k :=
  map_projected (Rat.castHom ℂ) k

end
end GUT.LiSixQuarkSeedRecipe
