import Math.RepresentationTheory.TripleMixedCoordinates

/-! Strictly sorted triple coordinates for alternating flavor tables. -/
namespace Math.TripleAlternatingCoordinates
set_option autoImplicit false
noncomputable section
abbrev Index (n : ℕ) := TripleMixedCoordinates.TripleIndex n
abbrev Coordinates (n : ℕ) := Index n → ℂ
abbrev Table (n : ℕ) := TripleMixedCoordinates.Table n
def Condition {n : ℕ} (u : Table n) : Prop :=
  (∀ x y z, u y x z = -u x y z) ∧ (∀ x y z, u x z y = -u x y z)
def extract {n : ℕ} (u : Table n) (p : Index n) : ℂ :=
  u p.val.1 p.val.2.1 p.val.2.2
def assemble {n : ℕ} (d : Coordinates n) (x y z : Fin n) : ℂ :=
  if he : x = y ∨ x = z ∨ y = z then 0
  else if hxy : x < y then
    if hyz : y < z then d ⟨(x,y,z), hxy, hyz⟩
    else if hxz : x < z then -d ⟨(x,z,y), hxz, by dsimp; omega⟩
    else d ⟨(z,x,y), by dsimp; omega, hxy⟩
  else if hxz : x < z then -d ⟨(y,x,z), by dsimp; omega, hxz⟩
  else if hyz : y < z then d ⟨(y,z,x), hyz, by dsimp; omega⟩
  else -d ⟨(z,y,x), by dsimp; omega, by dsimp; omega⟩

theorem extract_assemble {n : ℕ} (d : Coordinates n) : extract (assemble d) = d := by
  funext p
  rcases p with ⟨⟨x,y,z⟩,hxy,hyz⟩
  dsimp at hxy hyz
  simp [extract, assemble, hxy, hyz, ne_of_lt hxy, ne_of_lt hyz,
    ne_of_lt (lt_trans hxy hyz)]

theorem assemble_extract {n : ℕ} (u : Table n) (hu : Condition u) :
    assemble (extract u) = u := by
  funext x y z
  obtain ⟨h01,h12⟩ := hu
  by_cases he : x = y ∨ x = z ∨ y = z
  · simp [assemble, he]
    rcases he with he | he | he
    · subst y
      have hh := h01 x x z
      linear_combination (-1/2 : ℂ) * hh
    · subst z
      have hh := h12 x y x
      have hh' := h01 x x y
      linear_combination -hh + (1/2 : ℂ) * hh'
    · subst z
      have hh := h12 x y y
      linear_combination (-1/2 : ℂ) * hh
  · simp only [assemble, dite_eq_right he]
    split_ifs <;> simp only [extract]
    · linear_combination -h12 x y z
    · linear_combination h01 x z y - h12 x y z
    · linear_combination -h01 x y z
    · linear_combination h12 y x z - h01 x y z
    · linear_combination -h01 y z x + h12 y x z - h01 x y z

theorem condition_assemble {n : ℕ} (d : Coordinates n) : Condition (assemble d) := by
  constructor <;> intro x y z
  all_goals
    rcases lt_trichotomy x y with hxy | hxy | hxy <;>
      rcases lt_trichotomy x z with hxz | hxz | hxz <;>
      rcases lt_trichotomy y z with hyz | hyz | hyz
  all_goals try omega
  all_goals simp_all [assemble, ne_of_lt, ne_of_gt, not_lt_of_ge, le_of_lt]

def space (n : ℕ) : Submodule ℂ (Table n) where
  carrier := {u | Condition u}
  zero_mem' := by constructor <;> intros <;> simp
  add_mem' := by
    rintro u v ⟨hu,hu'⟩ ⟨hv,hv'⟩
    constructor <;> intro x y z
    · change u y x z + v y x z = -(u x y z + v x y z)
      rw [hu, hv]; ring
    · change u x z y + v x z y = -(u x y z + v x y z)
      rw [hu', hv']; ring
  smul_mem' := by
    rintro a u ⟨hu,hu'⟩
    constructor <;> intro x y z
    · change a * u y x z = -(a * u x y z); rw [hu]; ring
    · change a * u x z y = -(a * u x y z); rw [hu']; ring

def equiv (n : ℕ) : space n ≃ₗ[ℂ] Coordinates n where
  toFun u := extract u.val
  invFun d := ⟨assemble d, condition_assemble d⟩
  left_inv u := Subtype.ext (assemble_extract u.val u.property)
  right_inv := extract_assemble
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end
end Math.TripleAlternatingCoordinates
