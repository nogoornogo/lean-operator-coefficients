import Physics.StandardModel.Operators.QqueCoefficientCompleteness
import Physics.StandardModel.Gauge.LightSMFieldExtraction
import Math.RepresentationTheory.Multiplicity.MultiplicityDuality
import Math.RepresentationTheory.Multiplicity.MultiplicityTransport

open Math

/-! Complete qque classification on full standard-species evaluation images. -/
namespace GUT.FullLightSpeciesQque
noncomputable section
open Representation ProductFactorization StandardSMGaugeTensor
open ExternalInvariantTensor MultiplicityEvaluationImage

variable {H K : Type*} [Group H]
  [AddCommGroup K] [Module ℂ K] [FiniteDimensional ℂ K]
  (tau : Representation ℂ (GaugeGroup × H) K)

/-- No selected constituent: every standard-species intertwiner contributes. -/
abbrev Q := image tau quark
abbrev U := image tau.dual upRight
abbrev E := image tau.dual electronRight

omit [FiniteDimensional ℂ K] in
theorem quark_mem (f : MultiplicitySpace tau quark) (x : Quark) :
    f x ∈ Q tau := ⟨x ⊗ₜ[ℂ] f, rfl⟩

omit [FiniteDimensional ℂ K] in
theorem up_mem (f : MultiplicitySpace tau.dual upRight) (x : SMEpsilonTensor.Color) :
    f x ∈ U tau := ⟨x ⊗ₜ[ℂ] f, rfl⟩

omit [FiniteDimensional ℂ K] in
theorem electron_mem (f : MultiplicitySpace tau.dual electronRight) (x : ℂ) :
    f x ∈ E tau := ⟨x ⊗ₜ[ℂ] f, rfl⟩

variable (hs : IsSemisimpleRepresentation (firstRestriction tau))

def rightMultiplicityEquiv {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (r : Representation ℂ GaugeGroup V)
    [IsIrreducible r.dual] :
    Representation.Equiv (multiplicityRepresentation tau.dual r)
      (multiplicityRepresentation tau r.dual).dual :=
  (MultiplicityTransport.source tau.dual (SplitRepresentationProjection.bidualEquiv r)).trans
    (MultiplicityDuality.equiv tau r.dual hs)

def quarkEquiv : Representation.Equiv (Q tau).toRepresentation
    (external quark (multiplicityRepresentation tau quark)) := by
  letI : IsIrreducible quark := StandardSMIrreducibility.quark_irreducible
  exact (MultiplicityEvaluationImage.equiv tau quark).symm

def upEquiv : Representation.Equiv (U tau).toRepresentation
    (external upRight (multiplicityRepresentation tau upRight.dual).dual) := by
  letI : IsIrreducible upRight := StandardSMIrreducibility.upRight_irreducible
  letI : IsIrreducible upRight.dual := StandardSMIrreducibility.upLeft_irreducible
  let em := rightMultiplicityEquiv tau hs upRight
  let eg : Representation.Equiv
      (external upRight (multiplicityRepresentation tau.dual upRight))
      (external upRight (multiplicityRepresentation tau upRight.dual).dual) :=
    externalEquiv (Representation.Equiv.refl upRight) em
  exact (MultiplicityEvaluationImage.equiv tau.dual upRight).symm.trans eg

def electronEquiv : Representation.Equiv (E tau).toRepresentation
    (external electronRight (multiplicityRepresentation tau electronRight.dual).dual) := by
  letI : IsIrreducible electronRight := StandardSMIrreducibility.electronRight_irreducible
  letI : IsIrreducible electronRight.dual := StandardSMIrreducibility.electronLeft_irreducible
  let em := rightMultiplicityEquiv tau hs electronRight
  let eg : Representation.Equiv
      (external electronRight (multiplicityRepresentation tau.dual electronRight))
      (external electronRight (multiplicityRepresentation tau electronRight.dual).dual) :=
    externalEquiv (Representation.Equiv.refl electronRight) em
  exact (MultiplicityEvaluationImage.equiv tau.dual electronRight).symm.trans eg

def fields : LightSMFieldExtraction.Fields tau where
  Q := Q tau
  U := U tau
  E := E tau
  quarkEquiv := quarkEquiv tau
  upEquiv := upEquiv tau hs
  electronEquiv := electronEquiv tau hs

abbrev Sector := QqueCoefficientSector.sector
  (Q tau).toRepresentation (U tau).toRepresentation (E tau).toRepresentation

abbrev ResidualHom := IntertwiningMap
  ((multiplicityRepresentation tau quark).symmetricPower 2)
  ((multiplicityRepresentation tau upRight.dual).tprod
    (multiplicityRepresentation tau electronRight.dual))

/-- Named predicates keep model adapters from repeatedly expanding the large
actual-field types. Their contents are the full, independently defined sector. -/
def HasCoefficient : Prop := ∃ f : Sector tau, f ≠ 0

def HasResidualMap : Prop := ∃ k : ResidualHom tau, k ≠ 0

/-- Existing field certificates also use the full multiplicities. No positivity
or selected irreducible is needed to compare their coefficient spaces. -/
def suppliedFieldsEquiv (f : LightSMFieldExtraction.Fields tau) :
    ResidualHom tau ≃ₗ[ℂ] QqueCoefficientSector.sector
      f.Q.toRepresentation f.U.toRepresentation f.E.toRepresentation :=
  QqueCoefficientCompleteness.onFieldsEquiv _ _ _ _ _ _
    f.quarkEquiv f.upEquiv f.electronEquiv

def equiv : ResidualHom tau ≃ₗ[ℂ] Sector tau :=
  QqueCoefficientCompleteness.onFieldsEquiv _ _ _ _ _ _
    (fields tau hs).quarkEquiv (fields tau hs).upEquiv (fields tau hs).electronEquiv

include hs in
theorem nonzero_iff : (∃ f : Sector tau, f ≠ 0) ↔
    ∃ k : ResidualHom tau, k ≠ 0 :=
  QqueCoefficientCompleteness.exists_on_fields_iff _ _ _ _ _ _
    (fields tau hs).quarkEquiv (fields tau hs).upEquiv (fields tau hs).electronEquiv

include hs in
theorem all_forbidden_iff : (∀ f : Sector tau, f = 0) ↔
    ∀ k : ResidualHom tau, k = 0 := by
  simpa only [not_exists, not_not] using not_congr (nonzero_iff tau hs)

include hs in
theorem supplied_alternation_iff (f : LightSMFieldExtraction.Fields tau) :
    QqueSpinorExterior.HasNonzeroAlternation
      f.Q.toRepresentation f.U.toRepresentation f.E.toRepresentation ↔
      ∃ c : Sector tau, c ≠ 0 :=
  (QqueCoefficientCompleteness.hasNonzeroAlternation_iff _ _ _ _ _ _
    f.quarkEquiv f.upEquiv f.electronEquiv).trans (nonzero_iff tau hs).symm

end
end GUT.FullLightSpeciesQque
