import GUT.SU6.Yukawa.StabilizerBasis
import GUT.SU6.Yukawa.FiveCouplings

open Physics

open Math

/-! All actual Yukawa evaluations at the specified vacuum lie in the
previously constructed five-dimensional mass family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU6YukawaImage
noncomputable section
open StandardSMUVFields StandardSMUVStabilizer SU6YukawaStabilizer
open SU6YukawaWeights SU6YukawaBasis SU6FiveCouplings

theorem dualBasis_probe (i : Fin 6) : dualBasis i = dualProbe i := by
  apply dualCoordinates.toLinearEquiv.injective
  change dualCoordinates (dualBasis i) = dualCoordinates (dualProbe i)
  apply LinearMap.ext
  intro v
  rw [dualBasis_coordinates, dualProbe_apply]

theorem exteriorBasis_probe : exteriorBasis (wedgeFive 0) = exteriorProbe := by
  apply exteriorCoordinates.toLinearEquiv.injective
  change exteriorCoordinates (exteriorBasis (wedgeFive 0)) = exteriorCoordinates exteriorProbe
  rw [exteriorBasis_coordinates, ExteriorSquareCoordinates.basis_apply]
  simp only [exteriorProbe, Representation.Equiv.apply_symm_apply, wedgeFive]
  congr 1
  funext j
  fin_cases j
  · rfl
  · funext i; fin_cases i <;> norm_num [sixth, Pi.single_apply, Fin.ext_iff]

theorem basis_probeQ : basis (exteriorLabel 0) = probeQ := by
  simp [basis, exteriorLabel, Module.Basis.prod_apply, probeQ, exteriorBasis_probe]

theorem basis_probeA (i : Fin 6) : basis (dualLabel false i) = probeA i := by
  simp [basis, dualLabel, Module.Basis.prod_apply, probeA, dualBasis_probe]

theorem basis_probeB (i : Fin 6) : basis (dualLabel true i) = probeB i := by
  simp [basis, dualLabel, Module.Basis.prod_apply, probeB, dualBasis_probe]
  rfl

theorem evaluation_eq_of_probes (H : Type*) [CommGroup H]
    (Y Z : WeylYukawaMass.EquivariantYukawa StandardSMUVYukawa.scalar.rho uvRho)
    (h : let B := Y.toLinearMap (StandardSMUVYukawa.vacuum H)
         let C := Z.toLinearMap (StandardSMUVYukawa.vacuum H)
         B probeQ (probeA 0) = C probeQ (probeA 0) ∧
         B probeQ (probeB 0) = C probeQ (probeB 0) ∧
         B (probeA 5) (probeA 5) = C (probeA 5) (probeA 5) ∧
         B (probeA 5) (probeB 5) = C (probeA 5) (probeB 5) ∧
         B (probeB 5) (probeB 5) = C (probeB 5) (probeB 5)) :
    Y.toLinearMap (StandardSMUVYukawa.vacuum H) =
      Z.toLinearMap (StandardSMUVYukawa.vacuum H) := by
  apply eq_of_entries _ _ (Y.symmetric _) (Z.symmetric _)
    (evaluation_phase H Y) (evaluation_phase H Z) (evaluation_swap H Y) (evaluation_swap H Z)
  · intro c
    cases c
    · simpa only [basis_probeQ, basis_probeA] using h.1
    · simpa only [basis_probeQ, basis_probeB] using h.2.1
  · intro c d
    cases c <;> cases d
    · simpa only [basis_probeA] using h.2.2.1
    · simpa only [basis_probeA, basis_probeB] using h.2.2.2.1
    · simp only [basis_probeA, basis_probeB]
      rw [(Y.symmetric _).eq (probeB 5) (probeA 5),
        (Z.symmetric _).eq (probeB 5) (probeA 5)]
      exact h.2.2.2.1
    · simpa only [basis_probeB] using h.2.2.2.2

theorem coupling_evaluation (H : Type*) [CommGroup H] (a b u v w : ℂ) :
    (coupling a b u v w).toLinearMap (StandardSMUVYukawa.vacuum H) =
      (mass H a b u v w).form :=
  (ProjectedYukawa.zeroBare_form (coupling a b u v w)
    (StandardSMGroup.withResidual H) (StandardSMUVYukawa.vacuum H)
    (StandardSMUVYukawa.vacuum_fixed H)).symm

theorem evaluation_mem_range (H : Type*) [CommGroup H]
    (Y : WeylYukawaMass.EquivariantYukawa StandardSMUVYukawa.scalar.rho uvRho) :
    Y.toLinearMap (StandardSMUVYukawa.vacuum H) ∈ (massMap H).range := by
  let B := Y.toLinearMap (StandardSMUVYukawa.vacuum H)
  let a := B probeQ (probeA 0)
  let b := B probeQ (probeB 0)
  let u := B (probeA 5) (probeA 5)
  let v := B (probeA 5) (probeB 5)
  let w := B (probeB 5) (probeB 5)
  refine ⟨![a, b, u, v, w], ?_⟩
  change (mass H a b u v w).form = _
  rw [← coupling_evaluation]
  symm
  apply evaluation_eq_of_probes H Y (coupling a b u v w)
  dsimp only
  rw [coupling_evaluation]
  have hp := probe_values H a b u v w
  exact ⟨hp.1.symm, hp.2.1.symm, hp.2.2.1.symm, hp.2.2.2.1.symm, hp.2.2.2.2.symm⟩

theorem realized_iff (H : Type*) [CommGroup H] (B : LinearMap.BilinForm ℂ UV) :
    (∃ Y : WeylYukawaMass.EquivariantYukawa StandardSMUVYukawa.scalar.rho uvRho,
      Y.toLinearMap (StandardSMUVYukawa.vacuum H) = B) ↔ B ∈ (massMap H).range := by
  constructor
  · rintro ⟨Y, rfl⟩
    exact evaluation_mem_range H Y
  · exact range_realized H B

end
end GUT.SU6YukawaImage
