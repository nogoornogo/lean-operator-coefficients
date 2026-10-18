import Math.Topology.CoveringHom
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Order.Compact

/-! Continuous scalar characters of compact simply connected groups.
Compactness removes the positive modulus; lifting the circle character to
the real additive group removes its phase. -/

set_option autoImplicit false

namespace Math.CompactCharacters

variable {H : Type*} [Group H] [TopologicalSpace H] [CompactSpace H]

theorem real_eq_zero (f : H →* Multiplicative ℝ) (hf : Continuous f) (g : H) :
    Multiplicative.toAdd (f g) = 0 := by
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (show ContinuousOn (fun y => Multiplicative.toAdd (f y)) Set.univ from hf.continuousOn)
  have hn (y : H) : Multiplicative.toAdd (f y) ≤ 0 := by
    have h := hx (Set.mem_univ (x * y))
    change Multiplicative.toAdd (f (x * y)) ≤ Multiplicative.toAdd (f x) at h
    rw [map_mul] at h
    change Multiplicative.toAdd (f x) + Multiplicative.toAdd (f y) ≤
      Multiplicative.toAdd (f x) at h
    linarith
  have hp := hn g⁻¹
  rw [map_inv] at hp
  change -Multiplicative.toAdd (f g) ≤ 0 at hp
  linarith [hn g]

theorem complex_norm_eq_one (f : H →* ℂ) (hf : Continuous f) (g : H) : ‖f g‖ = 1 := by
  have hnz (y : H) : f y ≠ 0 := by
    intro he
    have h := f.map_mul y y⁻¹
    rw [mul_inv_cancel, map_one, he, zero_mul] at h
    exact one_ne_zero h
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.norm.continuousOn
  have hle (y : H) : ‖f y‖ ≤ 1 := by
    have h := hx (Set.mem_univ (x * y))
    change ‖f (x * y)‖ ≤ ‖f x‖ at h
    rw [map_mul, norm_mul] at h
    nlinarith [norm_pos_iff.mpr (hnz x)]
  have hi : ‖f g‖ * ‖f g⁻¹‖ = 1 := by rw [← norm_mul, ← map_mul]; simp
  have hh := mul_le_mul_of_nonneg_left (hle g⁻¹) (norm_nonneg (f g))
  rw [hi, mul_one] at hh
  exact le_antisymm (hle g) hh

variable [IsTopologicalGroup H] [SimplyConnectedSpace H] [LocallyPathConnectedSpace H]

theorem circle_eq_one (f : H →* Circle) (hf : Continuous f) (g : H) : f g = 1 := by
  let p : Multiplicative ℝ →* Circle :=
    { toFun := fun t => Circle.exp (Multiplicative.toAdd t)
      map_one' := Circle.exp_zero
      map_mul' := Circle.exp_add }
  have hp : IsCoveringMap p := Circle.isCoveringMap_exp
  obtain ⟨l, hl, _⟩ := CoveringHom.existsUnique_lift p hp f hf
  have he := DFunLike.congr_fun hl.2 g
  change Circle.exp (Multiplicative.toAdd (l g)) = f g at he
  rw [real_eq_zero l hl.1, Circle.exp_zero] at he
  exact he.symm

theorem complex_eq_one (f : H →* ℂ) (hf : Continuous f) (g : H) : f g = 1 := by
  let c : H →* Circle :=
    { toFun := fun x => ⟨f x, mem_sphere_zero_iff_norm.mpr (complex_norm_eq_one f hf x)⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun x y => Subtype.ext (map_mul f x y) }
  exact congrArg (fun z : Circle => (z : ℂ)) (circle_eq_one c (hf.subtype_mk _) g)

end Math.CompactCharacters
