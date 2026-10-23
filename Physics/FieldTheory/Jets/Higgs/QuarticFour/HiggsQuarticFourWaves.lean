import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourInput
import Math.Algebra.Waves.ColoredFourWaveEvaluation

/-! Colored null, conserving waves annihilate the complete free Higgs relations.
No Lorentz/internal invariance of an individual wave functional is asserted. -/
namespace Physics.HiggsQuarticFourWaves
set_option autoImplicit false
noncomputable section
open Math MvPolynomial DerivativeLiteratureHiggs HiggsQuarticFourInput
open FourWaveEvaluation FourWavePolarization
variable (k : Fin 4 → Fin 4 → ℂ) (v : Label → Fin 4 → ℂ)

abbrev ev := ColoredFourWaveEvaluation.evaluation k v
abbrev onJets := ColoredFourWaveEvaluation.onJets k v

theorem seed_zero (hn : ∀ s, (k s 0)^2-(k s 1)^2-(k s 2)^2-(k s 3)^2 = 0)
    (j : Label) : ev k v (seed 0 0 j) = 0 := by
  simp only [seed,map_zero,zero_mul,add_zero]
  change ev k v (D 0 (D 0 (X (j,0)))-D 1 (D 1 (X (j,0)))-
    D 2 (D 2 (X (j,0)))-D 3 (D 3 (X (j,0)))) = 0
  simp only [map_sub,ColoredFourWaveEvaluation.derivative,ColoredFourWaveEvaluation.field_value]
  simp only [ColoredFourWaveEvaluation.d_linear]
  simp only [linear,← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro s _
  rw [← sub_smul,← sub_smul,← sub_smul]
  have hz : k s 0*(k s 0*v j s)-k s 1*(k s 1*v j s)-
      k s 2*(k s 2*v j s)-k s 3*(k s 3*v j s) = 0 := by
    linear_combination v j s * hn s
  rw [hz,zero_smul]

theorem ideal_zero (hn : ∀ s, (k s 0)^2-(k s 1)^2-(k s 2)^2-(k s 3)^2 = 0)
    {p : DerivativeLiteratureHiggs.A} (hp : p ∈ DifferentialEquation.ideal D (seeds 0 0)) : ev k v p = 0 := by
  have he : DifferentialEquation.ideal D (seeds 0 0) ≤ RingHom.ker (ev k v).toRingHom := by
    apply DifferentialEquation.minimal
    · rintro p ⟨j,rfl⟩
      exact seed_zero k v hn j
    · intro i p hp
      change ev k v (D i p) = 0
      rw [ColoredFourWaveEvaluation.derivative,show ev k v p = 0 from hp,map_zero]
  exact he hp

theorem relations_eq : P.relations = DifferentialEquation.combined D (seeds 0 0) :=
  Math.HiggsLagrangianInput.generated_relations 0 0

theorem annihilates (hc : ∀ i, ∑ s : Fin 4, k s i = 0)
    (hn : ∀ s, (k s 0)^2-(k s 1)^2-(k s 2)^2-(k s 3)^2 = 0) :
    P.relations ≤ (onJets k v).ker := by
  rw [relations_eq]
  apply sup_le
  · intro p hp
    change coefficient (ev k v p) = 0
    rw [ideal_zero k v hn hp,map_zero]
  · rintro _ ⟨w,rfl⟩
    induction w using Finsupp.induction_linear with
    | zero => simp
    | add u w hu hw => simpa only [map_add] using (onJets k v).ker.add_mem hu hw
    | single i p =>
      rw [DifferentialEquation.divergence_single]
      exact ColoredFourWaveEvaluation.divergence_zero k v hc i p

end
end Physics.HiggsQuarticFourWaves
