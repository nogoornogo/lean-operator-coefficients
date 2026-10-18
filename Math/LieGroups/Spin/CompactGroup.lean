import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Compact
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Covering
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Connected

/-! Compact real Spin groups with the existing Clifford-algebra subtype
topology. In particular, Spin(10) is not SO(10) or split Spin(5,5). -/

set_option autoImplicit false

namespace Math.CompactSpin

noncomputable section

abbrev Group (n : ℕ) := CliffordAlgebra.realCliffordSpinGroupZero n
abbrev Orthogonal (n : ℕ) :=
  TauCeti.QuadraticMap.specialOrthogonalGroup (TauCeti.realCliffordForm n 0)

def projection (n : ℕ) [NeZero n] : Group n →* Orthogonal n :=
  (CliffordAlgebra.realCliffordSpinDoubleCoverZero n).rightHom

theorem projection_surjective (n : ℕ) [NeZero n] : Function.Surjective (projection n) :=
  (CliffordAlgebra.realCliffordSpinDoubleCoverZero n).rightHom_surjective

theorem projection_continuous (n : ℕ) [NeZero n] : Continuous (projection n) :=
  CliffordAlgebra.continuous_realCliffordSpinDoubleCoverZero_rightHom n

theorem projection_covering (n : ℕ) [NeZero n] : IsCoveringMap (projection n) :=
  CliffordAlgebra.isCoveringMap_realCliffordSpinDoubleCoverZero_rightHom n

theorem projection_fiber_card (n : ℕ) [NeZero n] (g : Orthogonal n) :
    Nat.card ((projection n) ⁻¹' {g}) = 2 :=
  CliffordAlgebra.card_fiber_realCliffordSpinDoubleCoverZero_rightHom n g

theorem projection_not_injective (n : ℕ) [NeZero n] :
    ¬ Function.Injective (projection n) := by
  obtain ⟨x, y, hxy, _⟩ := Nat.card_eq_two_iff.mp (projection_fiber_card n 1)
  intro hi
  exact hxy (Subtype.ext (hi (x.property.trans y.property.symm)))

theorem compact (n : ℕ) : CompactSpace (Group n) := inferInstance

theorem pathConnected (n : ℕ) : PathConnectedSpace (Group (n + 2)) :=
  CliffordAlgebra.pathConnectedSpace_realCliffordSpinGroupZero_add_two n

end

end Math.CompactSpin
