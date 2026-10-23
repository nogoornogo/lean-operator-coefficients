import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveInternalFields
import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveLorentz

/-! Actual internal-group invariance of the full-relation wave sum on the
whole selected grade. Unbounded invariance outside that grade is not needed. -/
namespace Physics.WeylHiggsWaveInternal
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear PairedWeylKinetic WeylHiggsInput WeylHiggsFirstTensor
open WeylHiggsEvenValue WeylHiggsInternalLift WeylHiggsWaveWords WeylHiggsWaveMoments
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

theorem psi_internal (c : Bool) (g : StandardSMGaugeTensor.GaugeGroup) (a : Fin 2) :
    action (g,1) (psi c a) = StandardSMGaugeTensor.phase (charge c) g • psi c a := by
  have he := WeylHiggsCurrent.psi_covariant c (g,1) a
  simpa only [map_one,Module.End.one_apply] using he

theorem derivative_internal (g : StandardSMGaugeTensor.GaugeGroup) (i : Fin 4) (p : A) :
    action (g,1) (D i p) = D i (action (g,1) p) := by
  have hd : directions (g,1) = 1 := LorentzDirections.direction.map_one
  simpa only [hd,Module.End.one_apply,Finsupp.single_apply,ite_smul,one_smul,zero_smul,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true] using derivative_covariant (g,1) i p

theorem derivative_psi_internal (c : Bool) (g : StandardSMGaugeTensor.GaugeGroup)
    (a : Fin 2) (i : Fin 4) :
    action (g,1) (D i (psi c a)) = StandardSMGaugeTensor.phase (charge c) g • D i (psi c a) := by
  rw [derivative_internal,psi_internal,map_smul]

theorem positive_odd_zero (g : StandardSMGaugeTensor.GaugeGroup) (c : Bool) (a : Fin 2)
    (i : Fin 4) (u v : A) :
    WeylHiggsWaveSum.functional (action (g,1) (u*D i (psi c a)*v)) = 0 := by
  rw [WeylHiggsCurrent.action_mul,WeylHiggsCurrent.action_mul,derivative_psi_internal,
    mul_smul_comm,smul_mul_assoc,map_smul,functional_positive_odd,smul_zero]

theorem primitive_covariant (g : StandardSMGaugeTensor.GaugeGroup) (c d : Bool) (a e : Fin 2)
    (q : DerivativeLiteratureHiggs.A) :
    action (g,1) (psi c a*psi d e*scalarEmbed q) =
      (StandardSMGaugeTensor.phase (charge c) g*StandardSMGaugeTensor.phase (charge d) g) •
        (psi c a*psi d e*scalarEmbed (HiggsQuarticFourInternalControls.T g q)) := by
  rw [WeylHiggsCurrent.action_mul,WeylHiggsCurrent.action_mul,psi_internal,psi_internal,scalar_internal,
    smul_mul_assoc,mul_smul_comm,smul_smul,smul_mul_assoc]

theorem primitive_invariant (g : StandardSMGaugeTensor.GaugeGroup) (c d : Bool) (a e : Fin 2)
    (b : Fin 4 → Label) (i : Fin 4) :
    WeylHiggsWaveSum.functional (action (g,1) (psi c a*psi d e*scalarEmbed (scalarMono b i))) =
      WeylHiggsWaveSum.functional (psi c a*psi d e*scalarEmbed (scalarMono b i)) := by
  rw [primitive_covariant,map_smul]
  cases c <;> cases d
  · simp only [functional_scalar_same,smul_zero]
  · rw [WeylHiggsCurrent.phases,one_smul]
    exact WeylHiggsWaveInternalFields.scalar_invariant g false true a e b i
  · have hp : StandardSMGaugeTensor.phase (charge true) g*StandardSMGaugeTensor.phase (charge false) g = 1 := by
      rw [mul_comm]
      exact WeylHiggsCurrent.phases g
    rw [hp,one_smul]
    exact WeylHiggsWaveInternalFields.scalar_invariant g true false a e b i
  · simp only [functional_scalar_same,smul_zero]

theorem first_word_invariant (g : StandardSMGaugeTensor.GaugeGroup) (c d : Bool) (b : Fin 4 → Label)
    (i : Fin 4) (a e : Fin 2) :
    WeylHiggsWaveSum.functional (action (g,1) (word c d b 0 (Finsupp.single i 1)
      (Finsupp.single a 1) (Finsupp.single e 1))) =
        WeylHiggsWaveSum.functional (word c d b 0 (Finsupp.single i 1)
          (Finsupp.single a 1) (Finsupp.single e 1)) := by
  have hz : WeylHiggsWaveSum.functional (action (g,1) (word c d b 0 (Finsupp.single i 1)
      (Finsupp.single a 1) (Finsupp.single e 1))) = 0 := by
    rw [first_word_scalar]
    have h0 := positive_odd_zero g c a i (1 : A) (psi d e*scalarEmbed (scalarProduct b))
    simpa only [one_mul,mul_assoc] using h0
  exact hz.trans (first_word_zero c d b a e i).symm

theorem second_word_invariant (g : StandardSMGaugeTensor.GaugeGroup) (c d : Bool) (b : Fin 4 → Label)
    (i : Fin 4) (a e : Fin 2) :
    WeylHiggsWaveSum.functional (action (g,1) (word c d b 1 (Finsupp.single i 1)
      (Finsupp.single a 1) (Finsupp.single e 1))) =
        WeylHiggsWaveSum.functional (word c d b 1 (Finsupp.single i 1)
          (Finsupp.single a 1) (Finsupp.single e 1)) := by
  have hz : WeylHiggsWaveSum.functional (action (g,1) (word c d b 1 (Finsupp.single i 1)
      (Finsupp.single a 1) (Finsupp.single e 1))) = 0 := by
    rw [second_word_scalar]
    exact positive_odd_zero g d e i (psi c a) (scalarEmbed (scalarProduct b))
  exact hz.trans (second_word_zero c d b a e i).symm

theorem even_word_invariant (g : StandardSMGaugeTensor.GaugeGroup) (c d : Bool) (b : Fin 4 → Label)
    (i : Fin 4) (a e : Fin 2) :
    WeylHiggsWaveSum.functional (action (g,1) (word c d b 2 (Finsupp.single i 1)
      (Finsupp.single a 1) (Finsupp.single e 1))) =
        WeylHiggsWaveSum.functional (word c d b 2 (Finsupp.single i 1)
          (Finsupp.single a 1) (Finsupp.single e 1)) := by
  rw [even_word_scalar]
  change WeylHiggsWaveSum.functional (action (g,1) (psi c a*psi d e*scalarEmbed (scalarMono b i))) =
    WeylHiggsWaveSum.functional (psi c a*psi d e*scalarEmbed (scalarMono b i))
  exact primitive_invariant g c d a e b i

theorem word_invariant (g : StandardSMGaugeTensor.GaugeGroup) (c d : Bool) (b : Fin 4 → Label)
    (r : Fin 3) (i : Fin 4) (a e : Fin 2) :
    WeylHiggsWaveSum.functional (action (g,1) (word c d b r (Finsupp.single i 1)
      (Finsupp.single a 1) (Finsupp.single e 1))) =
        WeylHiggsWaveSum.functional (word c d b r (Finsupp.single i 1)
          (Finsupp.single a 1) (Finsupp.single e 1)) := by
  fin_cases r
  · exact first_word_invariant g c d b i a e
  · exact second_word_invariant g c d b i a e
  · exact even_word_invariant g c d b i a e

theorem invariant (g : StandardSMGaugeTensor.GaugeGroup) (p : A) (hp : p ∈ V) :
    WeylHiggsWaveSum.functional (action (g,1) p) = WeylHiggsWaveSum.functional p := by
  have hs := WeylHiggsFirstSource.grade_le_span hp
  refine Submodule.span_induction (p := fun p _ =>
    WeylHiggsWaveSum.functional (action (g,1) p) = WeylHiggsWaveSum.functional p) ?_ ?_ ?_ ?_ hs
  · rintro p ⟨c,d,b,r,i,a,e,rfl⟩
    exact word_invariant g c d b r i a e
  · simp
  · intro p q _ _ hp hq
    simp only [map_add,hp,hq]
  · intro c p _ hp
    simp only [map_smul,hp]

end
end Physics.WeylHiggsWaveInternal
