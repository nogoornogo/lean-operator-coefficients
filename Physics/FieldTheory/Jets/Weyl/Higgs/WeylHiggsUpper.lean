import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsEvenCoordinates
import Math.RepresentationTheory.Relations.SelectedRelationExtension

/-! Candidate evaluation is injective on every admitted coefficient of the
entire actual C5 grade. No full-source invariant extension is assumed. -/
namespace Physics.WeylHiggsUpper
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear PairedWeylKinetic WeylHiggsInput WeylHiggsFirstTensor
open WeylHiggsLorentzUpper WeylHiggsInternalLift WeylHiggsEvenValue
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

theorem left_coordinate_zero (f : A →ₗ[ℂ] ℂ) (h : ∀ g p, p ∈ V → f (action g p) = f p)
    (hRel : input.relations ≤ f.ker) (hF : f DerivativeLiteratureMixed.candidate = 0)
    (b : Fin 4 → Label) : C f false true b 2 0 0 0 = 0 := by
  obtain ⟨i,hi⟩ := HiggsQuarticFourInternalControls.label_surjective (b 0)
  obtain ⟨j,hj⟩ := HiggsQuarticFourInternalControls.label_surjective (b 1)
  obtain ⟨k,hk⟩ := HiggsQuarticFourInternalControls.label_surjective (b 2)
  obtain ⟨l,hl⟩ := HiggsQuarticFourInternalControls.label_surjective (b 3)
  have hb : labels i j k l = b := by
    funext t
    fin_cases t <;> simp [labels,hi,hj,hk,hl]
  rw [← hb,← scalar_coordinate]
  exact all_scalar_zero f h hRel hF i j k l

theorem left_even_zero (f : A →ₗ[ℂ] ℂ) (h : ∀ g p, p ∈ V → f (action g p) = f p)
    (hRel : input.relations ≤ f.ker) (hF : f DerivativeLiteratureMixed.candidate = 0)
    (b : Fin 4 → Label) (a e : Fin 2) (i : Fin 4) : C f false true b 2 a e i = 0 := by
  rw [component_formula f h]
  simp only [Bool.false_eq_true,ite_false,ite_true,left_coordinate_zero f h hRel hF,zero_mul]

theorem bare_swap (c d : Bool) (a e : Fin 2) : psi c a*psi d e = -(psi d e*psi c a) := by
  have hs := MixedJetParity.odd_slide (I := Fin 4) ((c,a),0)
    (MixedJetAlgebra.odd (B := Label) ((d,e),0))
  rw [MixedJetParity.involute_odd] at hs
  exact hs.trans (neg_mul _ _)

theorem swap_even (f : A →ₗ[ℂ] ℂ) (c d : Bool) (b : Fin 4 → Label) (a e : Fin 2) (i : Fin 4) :
    C f c d b 2 a e i = -C f d c b 2 e a i := by
  rw [component_word,component_word,even_word_scalar,even_word_scalar,bare_swap,neg_mul,map_neg]

theorem even_zero (f : A →ₗ[ℂ] ℂ) (h : ∀ g p, p ∈ V → f (action g p) = f p)
    (hRel : input.relations ≤ f.ker) (hF : f DerivativeLiteratureMixed.candidate = 0)
    (c d : Bool) (b : Fin 4 → Label) (a e : Fin 2) (i : Fin 4) : C f c d b 2 a e i = 0 := by
  cases c <;> cases d
  · simpa only [Bool.false_eq_true,ite_false] using component_formula f h false false b 2 a e i
  · exact left_even_zero f h hRel hF b a e i
  · rw [swap_even,left_even_zero f h hRel hF,neg_zero]
  · simpa only [ite_true] using component_formula f h true true b 2 a e i

theorem whole_grade_zero (f : A →ₗ[ℂ] ℂ) (h : ∀ g p, p ∈ V → f (action g p) = f p)
    (hRel : input.relations ≤ f.ker) (hF : f DerivativeLiteratureMixed.candidate = 0)
    (p : A) (hp : p ∈ V) : f p = 0 := by
  apply WeylHiggsFirstSource.zero_of_words f ?_ p hp
  intro c d b r i a e
  rw [← component_word]
  fin_cases r
  · exact first_zero f h hRel c d b a e i
  · exact second_zero f h hRel c d b a e i
  · exact even_zero f h hRel hF c d b a e i

theorem selected_zero (F : selected.Coefficient) (hF : WeylHiggsSelection.evaluate F = 0) : F = 0 := by
  obtain ⟨f,hf,hRel⟩ := SelectedRelationExtension.exists_extension input V grade_stable F
  have h : ∀ g p, p ∈ V → f (action g p) = f p := by
    intro g p hp
    rw [hf ⟨action g p,grade_stable g hp⟩,hf ⟨p,hp⟩]
    exact F.val.isIntertwining _ _ g ⟨p,hp⟩
  have hc : f DerivativeLiteratureMixed.candidate = 0 := (hf WeylHiggsSelection.candidate).trans hF
  apply Subtype.ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro p
  change F.val p = 0
  exact (hf p).symm.trans (whole_grade_zero f h hRel hc p.val p.property)

theorem evaluate_injective : Function.Injective WeylHiggsSelection.evaluate := by
  intro F G h
  apply sub_eq_zero.mp
  apply selected_zero
  rw [map_sub,h,sub_self]

end
end Physics.WeylHiggsUpper
