import Physics.StandardModel.Gauge.StandardSMIrreducibility
import Math.RepresentationTheory.Multiplicity.EvaluationImage
import Math.RepresentationTheory.Decomposition.ExternalTensorDual

open Math

/-! Actual SM particle subspaces, extracted by evaluation and dual splitting.
The ambient representation may contain other species or vectorlike matter. -/

namespace GUT.LightSMFieldExtraction
noncomputable section
open Representation ProductFactorization ExternalInvariantTensor
open StandardSMGaugeTensor

variable {H V : Type*} [Group H]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (tau : Representation ℂ (GaugeGroup × H) V)

/-- A constructed identification with actual invariant subspaces, not an
identification with entire torus weight spaces. -/
structure Fields where
  Q : Subrepresentation tau
  U : Subrepresentation tau.dual
  E : Subrepresentation tau.dual
  quarkEquiv : Representation.Equiv Q.toRepresentation
    (external quark (multiplicityRepresentation tau quark))
  upEquiv : Representation.Equiv U.toRepresentation
    (external upRight (multiplicityRepresentation tau upRight.dual).dual)
  electronEquiv : Representation.Equiv E.toRepresentation
    (external electronRight (multiplicityRepresentation tau electronRight.dual).dual)

theorem nonempty_fields (ht : IsSemisimpleRepresentation tau) : Nonempty (Fields tau) := by
  let : IsIrreducible quark := StandardSMIrreducibility.quark_irreducible
  let : IsIrreducible upRight.dual := StandardSMIrreducibility.upLeft_irreducible
  let : IsIrreducible electronRight.dual := StandardSMIrreducibility.electronLeft_irreducible
  obtain ⟨U, ⟨eu⟩⟩ := MultiplicityEvaluationImage.exists_dual_image tau upRight.dual ht
  obtain ⟨E, ⟨ee⟩⟩ := MultiplicityEvaluationImage.exists_dual_image tau electronRight.dual ht
  exact ⟨{
    Q := MultiplicityEvaluationImage.image tau quark
    U := U
    E := E
    quarkEquiv := (MultiplicityEvaluationImage.equiv tau quark).symm
    upEquiv := eu.symm.trans
      (ExternalTensorDual.rightModelEquiv upRight (multiplicityRepresentation tau upRight.dual))
    electronEquiv := ee.symm.trans
      (ExternalTensorDual.rightModelEquiv electronRight
        (multiplicityRepresentation tau electronRight.dual)) }⟩

end
end GUT.LightSMFieldExtraction
