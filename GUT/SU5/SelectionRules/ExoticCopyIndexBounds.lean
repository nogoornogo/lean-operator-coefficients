import Mathlib.Tactic

/-! Explicit formal SM profiles only; no actual 40/50 branching equivalence. -/
namespace GUT.SU5.ExoticCopyIndexBounds
set_option autoImplicit false
open scoped BigOperators
abbrev Label := ℤ × ℤ × ℤ × ℤ
def profiles : Fin 4 → List Label := ![[(1, 0, 1, 1), (0, 1, 0, -4), (0, 0, 0, 6)], [(0, 1, 0, 2), (0, 0, 1, -3)], [(0, 2, 1, 1), (1, 1, 0, 6), (0, 1, 2, -4), (1, 0, 1, 1), (0, 1, 0, -4), (0, 0, 1, -9)], [(2, 0, 2, 2), (1, 1, 1, -3), (0, 2, 0, -8), (1, 0, 1, 7), (0, 1, 0, 2), (0, 0, 0, 12)]]
def conjugate (w : Label) : Label := (w.2.1,w.1,w.2.2.1,-w.2.2.2)
def index (r : Fin 4) (w : Label) : ℤ :=
  ((profiles r).count w : ℤ) - ((profiles r).count (conjugate w) : ℤ)
/-- E,L and two exotic spectator rows. -/
def rows : Fin 4 → Label := ![(0,0,0,6),(0,0,1,-3),(1,1,0,6),(0,0,0,12)]
theorem row_dictionary (r i : Fin 4) : index r (rows i) = if r=i then 1 else 0 := by
  revert r i
  decide +kernel

/-- Signed net copy coefficients; the premise is an explicit formal-index target. -/
theorem net_constraints (n : Fin 4 → ℤ) (N : ℤ)
    (h : ∀ i, ∑ r, n r * index r (rows i) = if i.val<2 then N else 0) :
    n 0 = N ∧ n 1 = N ∧ n 2 = 0 ∧ n 3 = 0 := by
  have hi (i : Fin 4) : n i = if i.val<2 then N else 0 := by
    simpa [row_dictionary] using h i
  exact ⟨by simpa using hi 0, by simpa using hi 1,
    by simpa using hi 2, by simpa using hi 3⟩

/-- Formal Q/U and E surpluses remain positive despite arbitrary exotic pairs. -/
theorem positive_surpluses (n : Fin 4 → ℤ) (N : ℤ) (hN : 0<N)
    (h : ∀ i, ∑ r, n r * index r (rows i) = if i.val<2 then N else 0) :
    0 < n 0+n 2 ∧ 0<n 0 := by
  obtain ⟨h0,_,h2,_⟩ := net_constraints n N h
  simp [h0,h2,hN]
end GUT.SU5.ExoticCopyIndexBounds
