import Math.RepresentationTheory.ColorInternalPairExclusion

/-! Complete positive support criterion for the actual restricted color
vertices occurring in signed SM core decompositions. The right side uses only
finite labelled contraction diagrams; no Hom or multiplicity remains. -/
namespace Math.ColorTreeSupport
set_option autoImplicit false
noncomputable section
open Representation ColorFlagTree ColorCertifiedTree ColorTensorTree

theorem positive_contraction_iff (t : Tree) (ht : Certified t) (k : ℕ)
    (h : positive (shape t) = negative (shape t)+3*k)
    (sigma : Equiv.Perm (Fin (negative (shape t)+3*k))) :
    (ColorTreeDiagrams.positiveContraction (shape t) k h sigma).comp (split t).embed ≠ 0 ↔
      ColorTreeDiagrams.PositiveValid (shape t) k h sigma := by
  constructor
  · intro hn
    constructor
    · intro s hs
      exact hn (ColorInternalPairExclusion.positive t ht k h sigma s hs)
    · intro a
      by_contra ha
      exact hn (positive_repeated_zero t ht k h sigma a ha)
  · intro hv he
    obtain ⟨a,ha⟩ := (ColorTreeDiagrams.positive_flag_iff (shape t) k h sigma).mpr hv
    have hz := DFunLike.congr_fun he (witness t a)
    change ColorTreeDiagrams.positiveContraction (shape t) k h sigma
      ((split t).embed (witness t a)) = 0 at hz
    rw [split_witness] at hz
    exact ha hz

theorem negative_contraction_iff (t : Tree) (ht : Certified t) (k : ℕ)
    (h : negative (shape t) = positive (shape t)+3*k)
    (sigma : Equiv.Perm (Fin (positive (shape t)+3*k))) :
    (ColorTreeDiagrams.negativeContraction (shape t) k h sigma).comp (split t).embed ≠ 0 ↔
      ColorTreeDiagrams.NegativeValid (shape t) k h sigma := by
  constructor
  · intro hn
    constructor
    · intro s hs
      exact hn (ColorInternalPairExclusion.negative t ht k h sigma s hs)
    · intro a
      by_contra ha
      exact hn (negative_repeated_zero t ht k h sigma a ha)
  · intro hv he
    obtain ⟨a,ha⟩ := (ColorTreeDiagrams.negative_flag_iff (shape t) k h sigma).mpr hv
    have hz := DFunLike.congr_fun he (witness t a)
    change ColorTreeDiagrams.negativeContraction (shape t) k h sigma
      ((split t).embed (witness t a)) = 0 at hz
    rw [split_witness] at hz
    exact ha hz

theorem positive_iff (t : Tree) (ht : Certified t) (k : ℕ)
    (h : positive (shape t) = negative (shape t)+3*k) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (ColorFlagTree.action t)) ↔
      ∃ sigma, ColorTreeDiagrams.PositiveValid (shape t) k h sigma :=
  (InvariantSpanningRestriction.allowed_iff (split t)
    (ColorTreeDiagrams.positiveContraction (shape t) k h)
    (ColorTreeDiagrams.positive_spanning (shape t) k h)).trans
      (exists_congr (positive_contraction_iff t ht k h))

theorem negative_iff (t : Tree) (ht : Certified t) (k : ℕ)
    (h : negative (shape t) = positive (shape t)+3*k) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (ColorFlagTree.action t)) ↔
      ∃ sigma, ColorTreeDiagrams.NegativeValid (shape t) k h sigma :=
  (InvariantSpanningRestriction.allowed_iff (split t)
    (ColorTreeDiagrams.negativeContraction (shape t) k h)
    (ColorTreeDiagrams.negative_spanning (shape t) k h)).trans
      (exists_congr (negative_contraction_iff t ht k h))

def DiagramSupport (t : Tree) : Prop :=
  (∃ k : Fin (positive (shape t)+1), ∃ h : positive (shape t)=negative (shape t)+3*k.val,
    ∃ sigma, ColorTreeDiagrams.PositiveValid (shape t) k.val h sigma) ∨
  (∃ k : Fin (negative (shape t)+1), ∃ h : negative (shape t)=positive (shape t)+3*k.val,
    ∃ sigma, ColorTreeDiagrams.NegativeValid (shape t) k.val h sigma)

theorem allowed_iff (t : Tree) (ht : Certified t) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (ColorFlagTree.action t)) ↔
      DiagramSupport t := by
  constructor
  · intro ha
    have hc := triality_necessary t ha
    by_cases hl : negative (shape t) ≤ positive (shape t)
    · let k := (positive (shape t)-negative (shape t))/3
      have h : positive (shape t)=negative (shape t)+3*k := by dsimp [k]; omega
      have hk : k<positive (shape t)+1 := by omega
      exact Or.inl ⟨⟨k,hk⟩,h,(positive_iff t ht k h).mp ha⟩
    · let k := (negative (shape t)-positive (shape t))/3
      have h : negative (shape t)=positive (shape t)+3*k := by dsimp [k]; omega
      have hk : k<negative (shape t)+1 := by omega
      exact Or.inr ⟨⟨k,hk⟩,h,(negative_iff t ht k h).mp ha⟩
  · rintro (⟨k,h,hv⟩ | ⟨k,h,hv⟩)
    · exact (positive_iff t ht k.val h).mpr hv
    · exact (negative_iff t ht k.val h).mpr hv

theorem forbidden_iff (t : Tree) (ht : Certified t) :
    SelectionCriteria.Forbidden (InvariantCoefficientTransport.Invariants (ColorFlagTree.action t)) ↔
      ¬ DiagramSupport t := by
  rw [SelectionCriteria.forbidden_iff_not_allowed,allowed_iff t ht]

end
end Math.ColorTreeSupport
