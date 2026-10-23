import Physics.StandardModel.Operators.Higgs.FourFamilyHiggsContent
import Physics.StandardModel.Operators.Support.Lepton.SMLowerHiggsSupport
import Physics.StandardModel.Operators.Support.Joint.SMMixedConjugation
import Math.RepresentationTheory.Constructions.MixedSupportSeparation

/-! Complete four-family mixed support on the common original-field interface.
The existing statistics-aware certificates are used through explicit space
isomorphisms; no exact multiplicity or numerical test is used. -/
namespace Physics.SMMixedFamilySupport
set_option autoImplicit false
noncomputable section
open Math Representation
open scoped TensorProduct

abbrev pattern := DeltaLOneFourFamilyDecomposition.pattern

theorem counts_iff (i : Fin 4) (labels : Fin 4 → DeltaLOneSignedInput.Species) :
    DeltaLOneSignedInput.counts labels = DeltaLOneFourFamilyDecomposition.familyCounts i ↔
    ∀ s, (Finset.univ.filter (fun j => labels j=s)).card =
      (Finset.univ.filter (fun j => pattern i j=s)).card := by
  constructor
  · intro h s
    exact DeltaLOneFourFamilyDecomposition.multiplicities_eq_of_counts labels (pattern i)
      (h.trans (DeltaLOneFourFamilyDecomposition.counts_pattern i).symm) s
  · intro h
    rw [← DeltaLOneFourFamilyDecomposition.counts_pattern]
    unfold DeltaLOneSignedInput.counts
    congr 1 <;> exact h _

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

abbrev oldSpace (i : Fin 4) (h d : ℕ) :=
  FourFamilyHiggsContent.Space flavor (NeutralHiggsPowers.flavor (H := H)) i h d
abbrev originalSpace (i : Fin 4) (h d : ℕ) :=
  SMFiniteHiggsSupport.OriginalSpace flavor (pattern i) h d

theorem membership (i : Fin 4) (h d : ℕ)
    (f : InvariantCoefficientTransport.Invariants
      ((SMFiniteHiggsSupport.FullSource flavor (n := 4)).tprod
        ((SMFiniteHiggsSupport.Scalars (H := H)).symmetricPower (h+d)))) :
    f ∈ oldSpace flavor i h d ↔ f ∈ originalSpace flavor i h d := by
  have hs := MixedSupportSeparation.separated_iff f.toLinearMap
    (fun labels => DeltaLOneSignedInput.counts labels=DeltaLOneFourFamilyDecomposition.familyCounts i)
    (fun scalars => DuqlHiggsContent.scalarCount scalars 0=h ∧
      DuqlHiggsContent.scalarCount scalars 1=d)
  constructor
  · intro hf
    obtain ⟨hfermi,hscalar⟩ := hs.mp hf
    rw [SMFiniteHiggsSupport.mem_original_iff]
    constructor
    · intro scalars hbad w x
      exact hscalar scalars (by simpa only [not_and_or, DuqlHiggsContent.scalarCount] using hbad) w x
    · intro labels hbad v y
      exact hfermi labels (fun hc => hbad ((counts_iff i labels).mp hc)) v y
  · intro hf
    rw [SMFiniteHiggsSupport.mem_original_iff] at hf
    apply hs.mpr
    constructor
    · intro labels hbad v y
      exact hf.2 labels (fun hc => hbad ((counts_iff i labels).mpr hc)) v y
    · intro scalars hbad w x
      exact hf.1 scalars (by simpa only [not_and_or, DuqlHiggsContent.scalarCount] using hbad) w x

def equiv (i : Fin 4) (h d : ℕ) : oldSpace flavor i h d ≃ₗ[ℂ] originalSpace flavor i h d where
  toFun f := ⟨f.val,(membership flavor i h d f.val).mp f.property⟩
  invFun f := ⟨f.val,(membership flavor i h d f.val).mpr f.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {k : ℕ} [NeZero k] (q l : ZMod k)

omit flavor in
theorem original_ql_iff (i : Fin 4) (h d : ℕ) :
    SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) (pattern i) h d) ↔
      h=d ∧ 3*q+l=0 :=
  (SelectionCriteria.allowed_equiv (equiv (QLFiniteSupport.flavor q l) i h d)).symm.trans
    (FourFamilyHiggsContent.allowed_iff q l i h d)

omit flavor in
theorem original_ql_forbidden (i : Fin 4) (h d : ℕ) :
    SelectionCriteria.Forbidden
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) (pattern i) h d) ↔
      h ≠ d ∨ 3*q+l ≠ 0 := by
  rw [SelectionCriteria.forbidden_iff_not_allowed, original_ql_iff q l i h d]
  exact not_and_or

omit flavor in
theorem conjugate_original_ql_iff (i : Fin 4) (h d : ℕ) :
    SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l)
      (BnvLocalConjugation.opposite ∘ pattern i) h d) ↔ h=d ∧ 3*q+l=0 :=
  (SMMixedConjugation.original_ql_iff (pattern i) q l d h).symm.trans
    ((original_ql_iff q l i d h).trans (and_congr eq_comm Iff.rfl))

omit flavor in
theorem conjugate_original_ql_forbidden (i : Fin 4) (h d : ℕ) :
    SelectionCriteria.Forbidden (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l)
      (BnvLocalConjugation.opposite ∘ pattern i) h d) ↔ h ≠ d ∨ 3*q+l ≠ 0 := by
  rw [SelectionCriteria.forbidden_iff_not_allowed, conjugate_original_ql_iff q l i h d]
  exact not_and_or

omit flavor q l in
theorem factorwise_counterexample :
    SelectionCriteria.Forbidden (SMFiniteHiggsSupport.OriginalSpace
      (QLFiniteSupport.flavor (0 : ZMod k) 0) (SMLowerGenerationSupport.pattern 0 3) 0 0) ∧
    SelectionCriteria.Forbidden (SMFiniteHiggsSupport.OriginalSpace
      (QLFiniteSupport.flavor (0 : ZMod k) 0) (SMLowerGenerationSupport.pattern 3 1) 0 0) ∧
    SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace
      (QLFiniteSupport.flavor (0 : ZMod k) 0) (pattern 2) 0 0) := by
  refine ⟨?_,?_,?_⟩
  · exact (SMLowerHiggsSupport.quark_ql_lower_forbidden (0 : ZMod k) 0 3 (by omega) 0 0).mpr
      (Or.inr (Or.inl (by omega)))
  · exact (SMLowerHiggsSupport.lepton_ql_all_forbidden (0 : ZMod k) 0 1 0 0).mpr
      (Or.inr (Or.inl (by omega)))
  · exact (original_ql_iff (0 : ZMod k) 0 2 0 0).mpr ⟨rfl,by simp⟩

end
end Physics.SMMixedFamilySupport
