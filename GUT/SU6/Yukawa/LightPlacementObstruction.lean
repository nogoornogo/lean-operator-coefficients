import GUT.SU6.Yukawa.LightEquations

open Physics

/-! Changing couplings in the fixed generated family cannot remove the
first-five exterior components. No alternate vacuum or scalar is admitted. -/
namespace GUT.SU6LightPlacementObstruction
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Math SU6YukawaBasis
open StandardSMUVFields StandardSMUVStabilizer SU6YukawaLight

/-- Universal actual-radical inclusion, not a UV character argument. -/
theorem all_yukawas_untouched (H : Type*) [CommGroup H]
    (Y : WeylYukawaMass.EquivariantYukawa StandardSMUVYukawa.scalar.rho uvRho)
    (p : ExteriorSquareCoordinates.Pair 6) (hp : p.val.2 ≠ 5) :
    basis (.inl (.inl p)) ∈ (generatedMass H Y).radical.toSubmodule := by
  obtain ⟨c, he, _⟩ := all_yukawas H Y
  rw [he]
  exact untouched_light H _ _ _ _ _ p hp

/-- An intended light subspace that omits a forced component cannot be exact. -/
theorem no_exact_light_omitting (H : Type*) [CommGroup H]
    (Y : WeylYukawaMass.EquivariantYukawa StandardSMUVYukawa.scalar.rho uvRho)
    (L : Submodule ℂ UV) (p : ExteriorSquareCoordinates.Pair 6)
    (hp : p.val.2 ≠ 5) (hL : basis (.inl (.inl p)) ∉ L) :
    (generatedMass H Y).radical.toSubmodule ≠ L := by
  intro he
  apply hL
  rw [← he]
  exact all_yukawas_untouched H Y p hp

end
end GUT.SU6LightPlacementObstruction
