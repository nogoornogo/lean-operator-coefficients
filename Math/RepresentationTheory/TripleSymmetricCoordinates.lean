import Math.RepresentationTheory.TripleMixedCoordinates

/-! Explicit sorted-triple coordinates for symmetric flavor tables. -/
namespace Math.TripleSymmetricCoordinates
set_option autoImplicit false
noncomputable section
abbrev Index (n : ℕ) :=
  {p : Fin n × Fin n × Fin n // p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2}
abbrev Coordinates (n : ℕ) := Index n → ℂ
abbrev Table (n : ℕ) := TripleMixedCoordinates.Table n

def Condition {n : ℕ} (t : Table n) : Prop :=
  (∀ x y z, t y x z = t x y z) ∧ (∀ x y z, t x z y = t x y z)

def extract {n : ℕ} (t : Table n) (p : Index n) : ℂ :=
  t p.val.1 p.val.2.1 p.val.2.2

def assemble {n : ℕ} (d : Coordinates n) (x y z : Fin n) : ℂ :=
  if hxy : x ≤ y then
    if hyz : y ≤ z then d ⟨(x,y,z), hxy, hyz⟩
    else if hxz : x ≤ z then d ⟨(x,z,y), hxz, by dsimp; omega⟩
    else d ⟨(z,x,y), by dsimp; omega, hxy⟩
  else if hxz : x ≤ z then d ⟨(y,x,z), by dsimp; omega, hxz⟩
  else if hyz : y ≤ z then d ⟨(y,z,x), hyz, by dsimp; omega⟩
  else d ⟨(z,y,x), by dsimp; omega, by dsimp; omega⟩

theorem extract_assemble {n : ℕ} (d : Coordinates n) : extract (assemble d) = d := by
  funext p
  rcases p with ⟨⟨x,y,z⟩,hxy,hyz⟩
  dsimp at hxy hyz
  simp [extract, assemble, hxy, hyz]

theorem assemble_extract {n : ℕ} (t : Table n) (ht : Condition t) :
    assemble (extract t) = t := by
  funext x y z
  obtain ⟨h01,h12⟩ := ht
  unfold assemble
  split_ifs <;> simp only [extract]
  · exact h12 x y z
  · exact (h01 x z y).trans (h12 x y z)
  · exact h01 x y z
  · exact (h12 y x z).trans (h01 x y z)
  · exact (h01 y z x).trans ((h12 y x z).trans (h01 x y z))

theorem condition_assemble {n : ℕ} (d : Coordinates n) : Condition (assemble d) := by
  constructor <;> intro x y z
  all_goals
    rcases lt_trichotomy x y with hxy | hxy | hxy <;>
      rcases lt_trichotomy x z with hxz | hxz | hxz <;>
      rcases lt_trichotomy y z with hyz | hyz | hyz
  all_goals try omega
  all_goals simp_all [assemble, not_le_of_gt, le_of_lt]

def space (n : ℕ) : Submodule ℂ (Table n) where
  carrier := {t | Condition t}
  zero_mem' := by constructor <;> intros <;> rfl
  add_mem' := by
    rintro t u ⟨ht,ht'⟩ ⟨hu,hu'⟩
    constructor <;> intro x y z
    · change t y x z + u y x z = t x y z + u x y z; rw [ht, hu]
    · change t x z y + u x z y = t x y z + u x y z; rw [ht', hu']
  smul_mem' := by
    rintro a t ⟨ht,ht'⟩
    constructor <;> intro x y z
    · change a * t y x z = a * t x y z; rw [ht]
    · change a * t x z y = a * t x y z; rw [ht']

def equiv (n : ℕ) : space n ≃ₗ[ℂ] Coordinates n where
  toFun t := extract t.val
  invFun d := ⟨assemble d, condition_assemble d⟩
  left_inv t := Subtype.ext (assemble_extract t.val t.property)
  right_inv := extract_assemble
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end
end Math.TripleSymmetricCoordinates
