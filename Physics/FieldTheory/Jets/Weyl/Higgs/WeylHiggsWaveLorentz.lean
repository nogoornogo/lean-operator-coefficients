import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveMoments
import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsFirstSource

/-! The Grassmann wave sum is invariant under arbitrary actual Lorentz
elements on the entire selected source, by its proved first-word moments. -/
namespace Physics.WeylHiggsWaveLorentz
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear PairedWeylKinetic WeylHiggsInput WeylHiggsFirstTensor
open WeylHiggsWaveWords WeylHiggsWaveMoments

theorem tensor_zero (c d : Bool) (b : Fin 4 → Label) (r : Fin 3)
    (hz : ∀ a e i, WeylHiggsWaveSum.functional (word c d b r (Finsupp.single i 1)
      (Finsupp.single a 1) (Finsupp.single e 1)) = 0) :
    tensor WeylHiggsWaveSum.functional c d b r = 0 := by
  apply WeylDirectionInvariant.tensor_ext
  intro a e i
  change WeylHiggsWaveSum.functional (word c d b r (Finsupp.single i 1)
    (Finsupp.single a 1) (Finsupp.single e 1)) = 0
  exact hz a e i

theorem first_tensor_zero (c d : Bool) (b : Fin 4 → Label) :
    tensor WeylHiggsWaveSum.functional c d b 0 = 0 :=
  tensor_zero c d b 0 (first_word_zero c d b)
theorem second_tensor_zero (c d : Bool) (b : Fin 4 → Label) :
    tensor WeylHiggsWaveSum.functional c d b 1 = 0 :=
  tensor_zero c d b 1 (second_word_zero c d b)
theorem same_tensor_zero (c : Bool) (b : Fin 4 → Label) :
    tensor WeylHiggsWaveSum.functional c c b 2 = 0 := by
  apply tensor_zero
  intro a e i
  rw [WeylHiggsInternalLift.even_word_scalar,functional_scalar_same]

theorem invariant_of_zero {f : WeylDirectionInvariant.Tensor} (hf : f = 0) (c d : Bool)
    (g : LorentzDirections.Group) (x y : Spin) (u : Dir) :
    f (LorentzJetIBP.weyl c g x) (LorentzJetIBP.weyl d g y) (LorentzDirections.direction g u) =
      f x y u := by
  rw [hf]
  rfl

theorem tensor_invariant (c d : Bool) (b : Fin 4 → Label) (r : Fin 3)
    (g : LorentzDirections.Group) (x y : Spin) (u : Dir) :
    tensor WeylHiggsWaveSum.functional c d b r (LorentzJetIBP.weyl c g x)
      (LorentzJetIBP.weyl d g y) (LorentzDirections.direction g u) =
        tensor WeylHiggsWaveSum.functional c d b r x y u := by
  fin_cases r
  · exact invariant_of_zero (first_tensor_zero c d b) c d g x y u
  · exact invariant_of_zero (second_tensor_zero c d b) c d g x y u
  · cases c <;> cases d
    · exact invariant_of_zero (same_tensor_zero false b) false false g x y u
    · exact WeylDirectionInvariant.invariant_of_components
        (tensor WeylHiggsWaveSum.functional false true b 2) (4*marked b)
        (even_word_left b) g x y u
    · exact WeylDirectionInvariant.invariant_of_transposed_components
        (tensor WeylHiggsWaveSum.functional true false b 2) (-4*marked b)
        (even_word_right b) g x y u
    · exact invariant_of_zero (same_tensor_zero true b) true true g x y u

theorem word_invariant (g : LorentzDirections.Group) (c d : Bool) (b : Fin 4 → Label)
    (r : Fin 3) (i : Fin 4) (a e : Fin 2) :
    WeylHiggsWaveSum.functional (action (1,g) (word c d b r (Finsupp.single i 1)
      (Finsupp.single a 1) (Finsupp.single e 1))) =
        WeylHiggsWaveSum.functional (word c d b r (Finsupp.single i 1)
          (Finsupp.single a 1) (Finsupp.single e 1)) := by
  change WeylHiggsWaveSum.functional (transport (1,g) (word c d b r _ _ _)) = _
  rw [word_lorentz]
  exact tensor_invariant c d b r g _ _ _

theorem invariant (g : LorentzDirections.Group) (p : A) (hp : p ∈ V) :
    WeylHiggsWaveSum.functional (action (1,g) p) = WeylHiggsWaveSum.functional p := by
  have hs := WeylHiggsFirstSource.grade_le_span hp
  refine Submodule.span_induction (p := fun p _ =>
    WeylHiggsWaveSum.functional (action (1,g) p) = WeylHiggsWaveSum.functional p) ?_ ?_ ?_ ?_ hs
  · rintro p ⟨c,d,b,r,i,a,e,rfl⟩
    exact word_invariant g c d b r i a e
  · simp
  · intro p q _ _ hp hq
    simp only [map_add,hp,hq]
  · intro c p _ hp
    simp only [map_smul,hp]

end
end Physics.WeylHiggsWaveLorentz
