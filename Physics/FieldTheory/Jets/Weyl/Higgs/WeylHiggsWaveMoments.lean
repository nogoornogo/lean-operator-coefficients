import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveWords
import Physics.FieldTheory.Jets.WeylDirectionInvariant.Core.Tensor
import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsUpper

/-! Exact first-word moment formulas for both statistics and chirality
choices. The internal tensor is the invariant marked field/dual pairing. -/
namespace Physics.WeylHiggsWaveMoments
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear PairedWeylKinetic WeylHiggsInput WeylHiggsFirstTensor
open WeylHiggsEvenValue WeylHiggsInternalLift WeylHiggsWaveWords
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

def marked (b : Fin 4 → Label) : ℂ :=
  MarkedFieldPairing.marked (fun t => Finsupp.single (b t) 1)

theorem marked_color (b : Fin 4 → Label) : marked b = MarkedFieldPairing.sign (b 0)*color b := by
  rw [marked,MarkedFieldPairing.marked_basis,← color_pairing]

theorem left_even (b : Fin 4 → Label) (a e : Fin 2) (i : Fin 4) :
    WeylHiggsWaveSum.functional (psi false a*psi true e*scalarEmbed (scalarMono b i)) =
      (2*WeylDirectionInvariant.kernel a e i)*marked b := by
  rw [functional_scalar_left]
  simp_rw [boson_value]
  have hi (s : Fin 4) :
      (∑ x : Fin 2, ∑ y : Fin 2,
        (MarkedFieldPairing.sign (b 0)*WeylHiggsWaveSum.momentum s i)*quartic x y b) =
      (MarkedFieldPairing.sign (b 0)*WeylHiggsWaveSum.momentum s i)*color b := by
    simp only [color,Finset.mul_sum]
  simp_rw [hi]
  calc
    _ = (∑ s : Fin 4, WeylHiggsWaveSum.weight a e s*WeylHiggsWaveSum.momentum s i)*
        (MarkedFieldPairing.sign (b 0)*color b) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := by rw [WeylHiggsWaveSum.moment,marked_color]

theorem reverse_scalar (a e : Fin 2) (q : DerivativeLiteratureHiggs.A) :
    WeylHiggsWaveSum.functional (psi true a*psi false e*scalarEmbed q) =
      -WeylHiggsWaveSum.functional (psi false e*psi true a*scalarEmbed q) := by
  have hs : psi true a*psi false e = -(psi false e*psi true a) := by
    exact WeylHiggsUpper.bare_swap true false a e
  rw [hs,neg_mul,map_neg]

theorem right_even (b : Fin 4 → Label) (a e : Fin 2) (i : Fin 4) :
    WeylHiggsWaveSum.functional (psi true a*psi false e*scalarEmbed (scalarMono b i)) =
      -(2*WeylDirectionInvariant.kernel e a i)*marked b := by
  rw [reverse_scalar,left_even]
  ring

theorem first_word_zero (c d : Bool) (b : Fin 4 → Label) (a e : Fin 2) (i : Fin 4) :
    WeylHiggsWaveSum.functional (word c d b 0 (Finsupp.single i 1)
      (Finsupp.single a 1) (Finsupp.single e 1)) = 0 := by
  rw [first_word_scalar]
  have hz := functional_positive_odd c a i (1 : A) (psi d e*scalarEmbed (scalarProduct b))
  simpa only [one_mul,mul_assoc] using hz

theorem second_word_zero (c d : Bool) (b : Fin 4 → Label) (a e : Fin 2) (i : Fin 4) :
    WeylHiggsWaveSum.functional (word c d b 1 (Finsupp.single i 1)
      (Finsupp.single a 1) (Finsupp.single e 1)) = 0 := by
  rw [second_word_scalar]
  exact functional_positive_odd d e i (psi c a) (scalarEmbed (scalarProduct b))

theorem even_word_left (b : Fin 4 → Label) (a e : Fin 2) (i : Fin 4) :
    WeylHiggsWaveSum.functional (word false true b 2 (Finsupp.single i 1)
      (Finsupp.single a 1) (Finsupp.single e 1)) =
        (4*marked b)*WeylDirectionInvariant.contraction
          (WeylDirectionInvariant.S a) (WeylDirectionInvariant.S e) (LorentzFiniteControls.E i) := by
  rw [even_word_scalar]
  change WeylHiggsWaveSum.functional (psi false a*psi true e*scalarEmbed (scalarMono b i)) = _
  rw [left_even,WeylDirectionInvariant.contraction_basis]
  ring

theorem even_word_right (b : Fin 4 → Label) (a e : Fin 2) (i : Fin 4) :
    WeylHiggsWaveSum.functional (word true false b 2 (Finsupp.single i 1)
      (Finsupp.single a 1) (Finsupp.single e 1)) =
        (-4*marked b)*WeylDirectionInvariant.contraction
          (WeylDirectionInvariant.S e) (WeylDirectionInvariant.S a) (LorentzFiniteControls.E i) := by
  rw [even_word_scalar]
  change WeylHiggsWaveSum.functional (psi true a*psi false e*scalarEmbed (scalarMono b i)) = _
  rw [right_even,WeylDirectionInvariant.contraction_basis]
  ring

end
end Physics.WeylHiggsWaveMoments
