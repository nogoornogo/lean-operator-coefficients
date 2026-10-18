import Physics.StandardModel.Operators.SMFiniteWeakBranching
import Math.RepresentationTheory.SU2IsotypicModels

/-! The actual mixed source splits into complete weak isotypic pieces,
retaining the joint color, hypercharge and independent spin action on every
multiplicity. No chosen individual weak copy is declared invariant. -/
namespace GUT.SMJointWeakContent
set_option autoImplicit false
noncomputable section
open Math Representation ContinuousRepresentationScope

abbrev Color := Matrix.specialUnitaryGroup (Fin 3) ℂ
abbrev Remaining := (Color × Circle) × SMCombinedCompactAction.Spin

def reorder : SMCombinedCompactAction.Group ≃* (TauCeti.SU2 × Remaining) where
  toFun g := (g.1.2.1, ((g.1.1,g.1.2.2),g.2))
  invFun g := ((g.2.1.1,(g.1,g.2.1.2)),g.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem inverse_continuous : Continuous reorder.symm := by
  have hc : Continuous (fun x : TauCeti.SU2 × Remaining => x.2.1.1) :=
    continuous_fst.comp (continuous_fst.comp continuous_snd)
  have hz : Continuous (fun x : TauCeti.SU2 × Remaining => x.2.1.2) :=
    continuous_snd.comp (continuous_fst.comp continuous_snd)
  exact (hc.prodMk (continuous_fst.prodMk hz)).prodMk (continuous_snd.comp continuous_snd)

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

abbrev source := (SMCombinedCompactContinuity.sourceModel flavor p).comp reorder.symm.toMonoidHom

theorem source_continuous : IsJointlyContinuous (source flavor p) :=
  (SMCombinedCompactContinuity.source_continuous flavor p).comp
    ⟨reorder.symm.toMonoidHom, inverse_continuous⟩

theorem weak_restriction : ProductFactorization.firstRestriction (source flavor p) =
    SMFiniteWeakBranching.source flavor p := rfl

theorem bounded : BoundedTorusWeights.Bounded
    (ProductFactorization.firstRestriction (source flavor p)) TauCeti.SU2.torusHom
      (SMContentWeakBound.bound p) := by
  rw [weak_restriction]
  exact SMFiniteWeakBranching.source_bounded flavor p

abbrev Multiplicity (m : ℕ) := SU2IsotypicModels.Carrier (source flavor p) m
abbrev multiplicity (m : ℕ) := SU2IsotypicModels.action (source flavor p) m

theorem multiplicity_continuous (m : ℕ) : IsJointlyContinuous (multiplicity flavor p m) :=
  SU2IsotypicModels.continuous_action (source flavor p) m (source_continuous flavor p)

/-- Complete equivariant weak decomposition with the full remaining action. -/
def decomposition : Representation.Equiv
    (FiniteBlockHom.action (SU2IsotypicModels.piece (source flavor p) (SMContentWeakBound.bound p)))
    (source flavor p) :=
  SU2IsotypicModels.ofBound (source flavor p) (SMContentWeakBound.bound p)
    (source_continuous flavor p) (bounded flavor p)

end
end GUT.SMJointWeakContent
