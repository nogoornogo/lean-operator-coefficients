import Math.LieGroups.Spin.CompactGroup
import Math.Topology.CoveringHom

/-! The general lifting route into actual compact Spin. This does not assert
that SU(5) is simply connected or construct its realified SO(10) map. -/

set_option autoImplicit false

namespace Math.CompactSpin

theorem existsUnique_lift {H : Type*} [_root_.Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [SimplyConnectedSpace H] [LocallyPathConnectedSpace H]
    (n : ℕ) [NeZero n] (f : H →* Orthogonal n) (hf : Continuous f) :
    ∃! g : H →* Group n, Continuous g ∧ (projection n).comp g = f :=
  CoveringHom.existsUnique_lift (projection n) (projection_covering n) f hf

theorem exists_injective_lift {H : Type*} [_root_.Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [SimplyConnectedSpace H] [LocallyPathConnectedSpace H]
    (n : ℕ) [NeZero n] (f : H →* Orthogonal n) (hf : Continuous f)
    (hi : Function.Injective f) :
    ∃ g : H →* Group n, Continuous g ∧ Function.Injective g ∧ (projection n).comp g = f := by
  obtain ⟨g, ⟨hg, hp⟩, _⟩ := existsUnique_lift n f hf
  exact ⟨g, hg, CoveringHom.injective_of_comp hp hi, hp⟩

end Math.CompactSpin
