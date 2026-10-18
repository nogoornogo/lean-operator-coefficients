import Mathlib.Tactic

/-! Explicit finite coordinates for a last-two-symmetric tensor with zero
cyclic sum. Repeated indices are handled separately from distinct triples. -/
namespace Math.TripleMixedCoordinates
set_option autoImplicit false
noncomputable section

abbrev PairIndex (n : ℕ) := {p : Fin n × Fin n // p.1 ≠ p.2}
abbrev TripleIndex (n : ℕ) :=
  {p : Fin n × Fin n × Fin n // p.1 < p.2.1 ∧ p.2.1 < p.2.2}
abbrev Index (n : ℕ) := PairIndex n ⊕ (TripleIndex n × Fin 2)
abbrev Coordinates (n : ℕ) := Index n → ℂ
abbrev Table (n : ℕ) := Fin n → Fin n → Fin n → ℂ

def Condition {n : ℕ} (v : Table n) : Prop :=
  (∀ x y z, v x z y = v x y z) ∧
  (∀ x y z, v x y z + v y x z + v z x y = 0)

def extract {n : ℕ} (v : Table n) : Coordinates n
  | .inl p => v p.val.1 p.val.1 p.val.2
  | .inr (p, i) => if i = 0 then v p.val.1 p.val.2.1 p.val.2.2
    else v p.val.2.1 p.val.1 p.val.2.2

def assemble {n : ℕ} (d : Coordinates n) (x y z : Fin n) : ℂ :=
  if hxy : x = y then
    if hxz : x = z then 0 else d (.inl ⟨(x,z), hxz⟩)
  else if hxz : x = z then d (.inl ⟨(x,y), hxy⟩)
  else if hyz : y = z then -2 * d (.inl ⟨(y,x), Ne.symm hxy⟩)
  else if hxy' : x < y then
    if hyz' : y < z then d (.inr (⟨(x,y,z), hxy', hyz'⟩, 0))
    else if hxz' : x < z then
      d (.inr (⟨(x,z,y), hxz', by dsimp; omega⟩, 0))
    else
      d (.inr (⟨(z,x,y), by dsimp; omega, hxy'⟩, 1))
  else if hxz' : x < z then
    d (.inr (⟨(y,x,z), by dsimp; omega, hxz'⟩, 1))
  else if hyz' : y < z then
    -d (.inr (⟨(y,z,x), hyz', by dsimp; omega⟩, 0)) -
     d (.inr (⟨(y,z,x), hyz', by dsimp; omega⟩, 1))
  else -d (.inr (⟨(z,y,x), by dsimp; omega, by dsimp; omega⟩, 0)) -
    d (.inr (⟨(z,y,x), by dsimp; omega, by dsimp; omega⟩, 1))

theorem extract_assemble {n : ℕ} (d : Coordinates n) : extract (assemble d) = d := by
  funext p
  rcases p with p | ⟨p,i⟩
  · rcases p with ⟨⟨x,y⟩,h⟩
    simp [extract, assemble, h]
  · rcases p with ⟨⟨x,y,z⟩,hxy,hyz⟩
    dsimp at hxy hyz
    have h₁ : x ≠ y := ne_of_lt hxy
    have h₂ : x ≠ z := ne_of_lt (lt_trans hxy hyz)
    have h₃ : y ≠ z := ne_of_lt hyz
    have h₄ : ¬y < x := by omega
    fin_cases i <;> simp [extract, assemble, h₁, h₂, h₃, Ne.symm h₁,
      hxy, hyz, h₄]

theorem assemble_extract {n : ℕ} (v : Table n) (hv : Condition v) :
    assemble (extract v) = v := by
  funext x y z
  obtain ⟨hs,hc⟩ := hv
  by_cases hxy : x = y
  · subst y
    by_cases hxz : x = z
    · subst z
      simp [assemble]
      have hh := hc x x x
      linear_combination (-1/3 : ℂ) * hh
    · simp [assemble, hxz, extract]
  · by_cases hxz : x = z
    · subst z
      simp [assemble, hxy, extract]
      exact hs x y x
    · by_cases hyz : y = z
      · subst z
        simp [assemble, hxy, extract]
        have hh := hc x y y
        have hh' := hs y x y
        linear_combination -hh - 2 * hh'
      · by_cases hxy' : x < y
        · by_cases hyz' : y < z
          · simp [assemble, hxy, hxz, hyz, hxy', hyz', extract]
          · by_cases hxz' : x < z
            · simp [assemble, hxy, hxz, hyz, hxy', hyz', hxz', extract]
              exact hs x y z
            · simp [assemble, hxy, hxz, hyz, hxy', hyz', hxz', extract]
              exact hs x y z
        · by_cases hxz' : x < z
          · simp [assemble, hxy, hxz, hyz, hxy', hxz', extract]
          · by_cases hyz' : y < z
            · simp [assemble, hxy, hxz, hyz, hxy', hxz', hyz', extract]
              have hh := hc x y z
              have hh' := hs z x y
              have hh'' := hs y x z
              linear_combination -hh - hh' - hh''
            · simp [assemble, hxy, hxz, hyz, hxy', hxz', hyz', extract]
              have hh := hc x y z
              have hh' := hs z x y
              have hh'' := hs y x z
              linear_combination -hh - hh' - hh''

theorem condition_assemble {n : ℕ} (d : Coordinates n) : Condition (assemble d) := by
  constructor
  · intro x y z
    rcases lt_trichotomy x y with hxy | hxy | hxy <;>
      rcases lt_trichotomy x z with hxz | hxz | hxz <;>
      rcases lt_trichotomy y z with hyz | hyz | hyz
    all_goals try omega
    all_goals simp_all [assemble, ne_of_lt, ne_of_gt, not_lt_of_ge, le_of_lt]
  · intro x y z
    rcases lt_trichotomy x y with hxy | hxy | hxy <;>
      rcases lt_trichotomy x z with hxz | hxz | hxz <;>
      rcases lt_trichotomy y z with hyz | hyz | hyz
    all_goals try omega
    all_goals simp_all [assemble, ne_of_lt, ne_of_gt, not_lt_of_ge, le_of_lt]
    all_goals ring

def space (n : ℕ) : Submodule ℂ (Table n) where
  carrier := {v | Condition v}
  zero_mem' := by constructor <;> intros <;> simp
  add_mem' := by
    rintro v w ⟨hv,hv'⟩ ⟨hw,hw'⟩
    constructor
    · intro x y z; change v x z y + w x z y = v x y z + w x y z
      rw [hv, hw]
    · intro x y z
      have h₁ := hv' x y z
      have h₂ := hw' x y z
      change (v x y z + w x y z) + (v y x z + w y x z) +
        (v z x y + w z x y) = 0
      linear_combination h₁ + h₂
  smul_mem' := by
    rintro a v ⟨hv,hv'⟩
    constructor
    · intro x y z; change a * v x z y = a * v x y z; rw [hv]
    · intro x y z
      have hh := hv' x y z
      change a * v x y z + a * v y x z + a * v z x y = 0
      linear_combination a * hh

def equiv (n : ℕ) : space n ≃ₗ[ℂ] Coordinates n where
  toFun v := extract v.val
  invFun d := ⟨assemble d, condition_assemble d⟩
  left_inv v := Subtype.ext (assemble_extract v.val v.property)
  right_inv := extract_assemble
  map_add' v w := by
    funext p
    rcases p with p | ⟨p,i⟩
    · rfl
    · fin_cases i <;> rfl
  map_smul' a v := by
    funext p
    rcases p with p | ⟨p,i⟩
    · rfl
    · fin_cases i <;> rfl

theorem finrank_eq_index_card (n : ℕ) :
    Module.finrank ℂ (space n) = Fintype.card (Index n) := by
  rw [(equiv n).finrank_eq, Module.finrank_fintype_fun_eq_card]

theorem index_card_zero : Fintype.card (Index 0) = 0 := by decide +kernel
theorem index_card_one : Fintype.card (Index 1) = 0 := by decide +kernel
theorem index_card_two : Fintype.card (Index 2) = 2 := by decide +kernel
theorem index_card_three : Fintype.card (Index 3) = 8 := by decide +kernel

end
end Math.TripleMixedCoordinates
