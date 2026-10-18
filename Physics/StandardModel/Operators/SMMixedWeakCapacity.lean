import Math.RepresentationTheory.ContentTorusBound
import Physics.StandardModel.Operators.SMConstantWeakCapacity
import Physics.StandardModel.Operators.SMIteratedContent
import Physics.StandardModel.Operators.SMLowerHiggsSupport

/-! Actual mixed-content complementary weak capacities. This closes uniform
forbidden regions, without computing a character coefficient or a rank. -/
namespace GUT.SMMixedWeakCapacity
set_option autoImplicit false
noncomputable section
open Math Representation BoundedTorusWeights SMWeakWeightBasis

def speciesBound (s : DeltaLOneSignedInput.Species) (d : ℕ) : ℕ :=
  if doubletCount s = 0 then 0 else SMConstantWeakCapacity.bound s d

def bound {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species) : ℕ :=
  ∑ s, speciesBound s (SMIteratedContent.counts p s)

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

theorem exterior_bounded (s : DeltaLOneSignedInput.Species) (d : ℕ) :
    Bounded ((DeltaLOneSignedFields.field flavor s).exteriorPower d)
      (fullTorus (H := H)) (speciesBound s d) := by
  unfold speciesBound
  split_ifs with hs
  · have hb : Bounded (SMContentWeakBound.source flavor (SMConstantWeakCapacity.pattern s d))
        (fullTorus (H := H)) 0 := by
      simpa [SMContentWeakBound.bound,SMConstantWeakCapacity.pattern,hs] using
        SMContentWeakBound.source_bounded flavor (SMConstantWeakCapacity.pattern s d)
    exact bounded_of_surjective _ _ _
      (ConstantPatternExterior.equiv (DeltaLOneSignedFields.field flavor) s d).symm.toIntertwiningMap
      (ConstantPatternExterior.equiv (DeltaLOneSignedFields.field flavor) s d).symm.surjective _ hb
  · exact SMConstantWeakCapacity.exterior_bounded flavor s d

theorem source_bounded : Bounded (SMContentWeakBound.source flavor p)
    (fullTorus (H := H)) (bound p) :=
  ContentTorusBound.word (fullTorus (H := H)) 9
    (SMIteratedContent.leaves flavor (SMIteratedContent.counts p)) p (fun _ => rfl)
    (fun s => speciesBound s (SMIteratedContent.counts p s)) (fun s => exterior_bounded flavor s _)

theorem local_high_zero (m : ℕ) (delta : ℤ) (hm : bound p < m)
    (f : InvariantCoefficientTransport.Invariants (SMIntegralLocalWeights.action flavor p m delta)) :
    f=0 :=
  BoundedHiggsSupport.high_zero (SMIntegralLocalWeights.source flavor p)
    (SMHiggsConstituents.weakProjection.comp (MonoidHom.inl _ _))
    (SMHiggsConstituents.character.comp (MonoidHom.inl _ _))
    SMIntegralLocalWeights.weak (fun _ => rfl) (fun u => SMFiniteHiggsSupport.weak_character u)
    (bound p) m delta (source_bounded flavor p) hm f

theorem local_high_forbidden (m : ℕ) (delta : ℤ) (hm : bound p < m) :
    SelectionCriteria.Forbidden (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor p m delta)) := local_high_zero flavor p m delta hm

theorem saturated_bound_zero
    (hc : ∀ s, doubletCount s ≠ 0 → SMIteratedContent.counts p s=0 ∨
      SMIteratedContent.counts p s=SMConstantWeakCapacity.dimension s) : bound p=0 := by
  apply Finset.sum_eq_zero
  intro s _
  unfold speciesBound
  split_ifs with hs
  · rfl
  · rcases hc s hs with h | h <;> simp [SMConstantWeakCapacity.bound,h]

omit flavor in
theorem original_ql_forbidden {k : ℕ} [NeZero k] (q l : ZMod k) (h d : ℕ)
    (hd : (bound p : ℤ) < (h : ℤ)-d ∨ (h : ℤ)-d < -(bound p : ℤ)) :
    SelectionCriteria.Forbidden
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) := by
  rw [SelectionCriteria.forbidden_iff_not_allowed,QLFiniteSupport.original_allowed_iff]
  rintro ⟨_,m,had,ha⟩
  have hl := (SelectionCriteria.allowed_equiv (SMLowerHiggsSupport.qlLocalEquiv p q l m.val
    ((h : ℤ)-d))).mp ha
  have hm : bound p < m.val := by dsimp [BoundedHiggsSupport.Admissible] at had; omega
  exact (SelectionCriteria.forbidden_iff_not_allowed _).mp
    (local_high_forbidden (QLFiniteSupport.flavor q l) p m.val ((h : ℤ)-d) hm) hl

omit flavor in
theorem saturated_original_ql_forbidden {k : ℕ} [NeZero k] (q l : ZMod k) (h d : ℕ)
    (hc : ∀ s, doubletCount s ≠ 0 → SMIteratedContent.counts p s=0 ∨
      SMIteratedContent.counts p s=SMConstantWeakCapacity.dimension s) (hd : h ≠ d) :
    SelectionCriteria.Forbidden
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) := by
  apply original_ql_forbidden p q l h d
  rw [saturated_bound_zero p hc]
  omega

end
end GUT.SMMixedWeakCapacity
