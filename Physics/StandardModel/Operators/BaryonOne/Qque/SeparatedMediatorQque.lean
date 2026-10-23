import Math.RepresentationTheory.Decomposition.SeparatedMediator
import Physics.StandardModel.Operators.BaryonOne.Qque.QqueMediatorInheritance

open Math

/-! Representation separation derives the support and mass identities
needed for qque inheritance. Retained mass invertibility is constructed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Physics.SeparatedMediatorQque
noncomputable section
open Representation SeparatedMediator
open scoped TensorProduct

variable {H Q U E V W : Type*} [Group H]
  [AddCommGroup Q] [Module ℂ Q] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup E] [Module ℂ E] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  (q : Representation ℂ H Q) (u : Representation ℂ H U) (e : Representation ℂ H E)
  (r : Representation ℂ H V) (s : Representation ℂ H W)

def leftCore (J : IntertwiningMap (q.tprod u) (r.prod s)) : IntertwiningMap (q.tprod u) r :=
  (IntertwiningMap.fst ℂ r s).comp J

def rightCore (K : IntertwiningMap (q.tprod e) (r.prod s).dual) :
    IntertwiningMap (q.tprod e) r.dual :=
  (SplitRepresentationProjection.dualMap (IntertwiningMap.inl ℂ r s)).comp K

variable (hr : IsSemisimpleRepresentation r) (hrs : ¬ CommonIrreducible.Shares r s)
  (N : Representation.Equiv (r.prod s) (r.prod s)) (g : ℂ)
  (J : IntertwiningMap (q.tprod u) (r.prod s))
  (K : IntertwiningMap (q.tprod e) (r.prod s).dual)

theorem source_coefficient_eq (ha : IsSemisimpleRepresentation (q.tprod u))
    (has : ¬ CommonIrreducible.Shares (q.tprod u) s) :
    MediatorExchange.coefficient N.toLinearEquiv g J.toLinearMap K.toLinearMap =
      MediatorExchange.coefficient (coreMass r s hr hrs N).toLinearEquiv g
        (leftCore q u r s J).toLinearMap (rightCore q e r s K).toLinearMap := by
  apply MediatorInheritance.coefficient_of_source_support _ _ (LinearMap.inl ℂ V W) g
  · exact coreMass_compat r s hr hrs N
  · intro x
    exact source_support r s (q.tprod u) ha has J x
  · intro y x
    rfl

theorem observer_coefficient_eq (hs : IsSemisimpleRepresentation s)
    (hsr : ¬ CommonIrreducible.Shares s r)
    (ha : IsSemisimpleRepresentation (q.tprod e))
    (has : ¬ CommonIrreducible.Shares (q.tprod e) s.dual) :
    MediatorExchange.coefficient N.toLinearEquiv g J.toLinearMap K.toLinearMap =
      MediatorExchange.coefficient (coreMass r s hr hrs N).toLinearEquiv g
        (leftCore q u r s J).toLinearMap (rightCore q e r s K).toLinearMap := by
  apply MediatorInheritance.coefficient_of_observer_support _ _ (LinearMap.fst ℂ V W) g
  · exact projection_stable r s hs hsr N.toIntertwiningMap
  · intro x
    rfl
  · intro y x
    exact dual_support r s (q.tprod e) ha has K y x

omit hr hrs in
def fullSector := MediatorQque.sector q u e N.toLinearEquiv g J.toLinearMap K.toLinearMap
  (MediatorQque.invariant_of_equivariant q u e (r.prod s) N g J K)

def coreSector := MediatorQque.sector q u e (coreMass r s hr hrs N).toLinearEquiv g
  (leftCore q u r s J).toLinearMap (rightCore q e r s K).toLinearMap
  (MediatorQque.invariant_of_equivariant q u e r (coreMass r s hr hrs N) g
    (leftCore q u r s J) (rightCore q e r s K))

theorem sector_eq_of_source (ha : IsSemisimpleRepresentation (q.tprod u))
    (has : ¬ CommonIrreducible.Shares (q.tprod u) s) :
    fullSector q u e r s N g J K = coreSector q u e r s hr hrs N g J K := by
  exact QqueMediatorInheritance.sector_eq q u e _ _ g _ _ _ _
    (source_coefficient_eq q u e r s hr hrs N g J K ha has) _ _

theorem sector_eq_of_observer (hs : IsSemisimpleRepresentation s)
    (hsr : ¬ CommonIrreducible.Shares s r)
    (ha : IsSemisimpleRepresentation (q.tprod e))
    (has : ¬ CommonIrreducible.Shares (q.tprod e) s.dual) :
    fullSector q u e r s N g J K = coreSector q u e r s hr hrs N g J K := by
  exact QqueMediatorInheritance.sector_eq q u e _ _ g _ _ _ _
    (observer_coefficient_eq q u e r s hr hrs N g J K hs hsr ha has) _ _

theorem nonzero_of_source (ha : IsSemisimpleRepresentation (q.tprod u))
    (has : ¬ CommonIrreducible.Shares (q.tprod u) s)
    (hc : coreSector q u e r s hr hrs N g J K ≠ 0) :
    fullSector q u e r s N g J K ≠ 0 := by
  rw [sector_eq_of_source q u e r s hr hrs N g J K ha has]
  exact hc

end
end Physics.SeparatedMediatorQque
