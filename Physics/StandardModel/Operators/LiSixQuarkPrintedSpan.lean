import Physics.StandardModel.Operators.LiSixQuarkLocalBasis
import Physics.StandardModel.Operators.LiSixQuarkProbeDecomposition
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The printed orbit span is exactly the separating hyperplane. -/
namespace GUT.LiSixQuarkPrintedSpan
noncomputable section
open LiSixQuarkCertificate LiSixQuarkConvention LiSixQuarkExtension
open SixQuarkSpeciesQuotient

abbrev Array := Fin 5 → Fin 5 → ℂ

def printedSpan : Submodule ℂ Array := Submodule.span ℂ
  {c | ∃ (k : Fin 10) (w : List (Fin 4)),
    c = w.foldl (fun c g => transform c g) (seedCoordinates k.castSucc)}

theorem printedSpan_le_kernel : printedSpan ≤ LinearMap.ker extraProbeLinear := by
  apply Submodule.span_le.mpr
  rintro c ⟨k,w,rfl⟩
  exact printed_orbit_probe_zero k w

theorem selected_printed (j : Fin 24) : orbitArray j.castSucc ∈ printedSpan := by
  have hj : (selectedSeed j.castSucc).val < 10 := by
    fin_cases j <;> decide
  apply Submodule.subset_span
  refine ⟨⟨(selectedSeed j.castSucc).val, hj⟩, selectedWord j.castSucc, ?_⟩
  rfl

theorem last_orbit : orbitArray 24 = extra := by
  change seedCoordinates 10 = extra
  exact (LiSixQuarkSeedRecipe.rational_cast 10).trans LiSixQuarkReducedSeeds.extra_seed

theorem probe_assembly (v : Fin 25 → ℂ) : extraProbe (coordinateEquiv v) = v 24 := by
  have ha : coordinateEquiv v = ∑ j, v j • orbitArray j := by
    ext p q
    simpa [smul_eq_mul] using LiSixQuarkLocalBasis.coordinate_assembly v p q
  change extraProbeLinear (coordinateEquiv v) = _
  rw [ha, map_sum]
  simp only [map_smul]
  rw [Fin.sum_univ_castSucc]
  have hz : ∀ j : Fin 24, extraProbeLinear (orbitArray j.castSucc) = 0 := by
    intro j
    exact printedSpan_le_kernel (selected_printed j)
  simp only [hz, smul_zero, Finset.sum_const_zero, zero_add]
  simp [last_orbit, extraProbeLinear, extraProbe_extra]

theorem printedSpan_eq_kernel : printedSpan = LinearMap.ker extraProbeLinear := by
  apply le_antisymm printedSpan_le_kernel
  intro c hc
  let v := coordinateEquiv.symm c
  have hv : v 24 = 0 := by
    rw [← probe_assembly v, LinearEquiv.apply_symm_apply]
    exact hc
  have ha : c = ∑ j, v j • orbitArray j := by
    ext p q
    simpa [v, smul_eq_mul] using LiSixQuarkLocalBasis.coordinate_assembly v p q
  rw [ha, Fin.sum_univ_castSucc]
  change (∑ j : Fin 24, v j.castSucc • orbitArray j.castSucc) +
    v 24 • orbitArray 24 ∈ printedSpan
  rw [hv, zero_smul, add_zero]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (selected_printed j)

theorem printed_finrank : Module.finrank ℂ printedSpan = 24 := by
  rw [printedSpan_eq_kernel]
  exact probe_kernel_finrank

theorem printed_reconstruction (c : Array) (hc : c ∈ printedSpan) :
    c = ∑ j : Fin 24, coordinateEquiv.symm c j.castSucc • orbitArray j.castSucc := by
  have hz : coordinateEquiv.symm c 24 = 0 := by
    rw [← probe_assembly (coordinateEquiv.symm c), LinearEquiv.apply_symm_apply]
    exact printedSpan_le_kernel hc
  have ha : c = ∑ j : Fin 25, coordinateEquiv.symm c j • orbitArray j := by
    ext p q
    simpa [smul_eq_mul] using
      LiSixQuarkLocalBasis.coordinate_assembly (coordinateEquiv.symm c) p q
  calc
    c = ∑ j : Fin 25, coordinateEquiv.symm c j • orbitArray j := ha
    _ = _ := by
      rw [Fin.sum_univ_castSucc]
      change _ + coordinateEquiv.symm c 24 • orbitArray 24 = _
      rw [hz, zero_smul, add_zero]

end
end GUT.LiSixQuarkPrintedSpan
