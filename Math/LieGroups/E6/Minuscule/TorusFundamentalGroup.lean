import Math.LieGroups.E6.Minuscule.TorusLoopContraction
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-! The actual torus inclusion induces the trivial fundamental-group map.
Surjectivity of this map is not assumed or proved here. -/

set_option autoImplicit false

namespace Math.E6.Minuscule.Torus

noncomputable section

def fundamentalMap : FundamentalGroup Point 1 →* FundamentalGroup compactIdentityComponent 1 :=
  FundamentalGroup.mapOfEq ⟨hom, hom_continuous⟩ (map_one hom)

theorem fundamentalMap_loop (p : Path (1 : Point) 1) :
    fundamentalMap (Path.Homotopic.Quotient.mk p) =
      Path.Homotopic.Quotient.mk (loopImage p) := by
  rw [fundamentalMap, FundamentalGroup.mapOfEq_apply]
  rfl

theorem fundamentalMap_apply_eq_one (c : FundamentalGroup Point 1) : fundamentalMap c = 1 := by
  induction c using Path.Homotopic.Quotient.ind with
  | mk p =>
    rw [fundamentalMap_loop]
    exact Quotient.sound (loopImage_nullhomotopic p)

theorem fundamentalMap_trivial : fundamentalMap = 1 := by
  ext c
  exact fundamentalMap_apply_eq_one c

theorem fundamentalMap_range : fundamentalMap.range = ⊥ := by
  rw [fundamentalMap_trivial]
  simp

end

end Math.E6.Minuscule.Torus
