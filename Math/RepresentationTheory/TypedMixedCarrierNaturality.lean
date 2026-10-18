import Math.RepresentationTheory.TypedMixedSeparatedHom
import Math.RepresentationTheory.LocalRelationTensorNaturality

/-! The ordered and separated residual carriers are equivalent independently
of any functional completeness theorem. -/
namespace Math.TypedMixedCarrierNaturality
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {P Q G H : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [Group G] [Group H]
  {L M : P → Type*} {K N : Q → Type*}
  [∀ u, AddCommGroup (L u)] [∀ u, Module ℂ (L u)]
  [∀ u, AddCommGroup (M u)] [∀ u, Module ℂ (M u)]
  [∀ u, AddCommGroup (K u)] [∀ u, Module ℂ (K u)]
  [∀ u, AddCommGroup (N u)] [∀ u, Module ℂ (N u)]
  (a : ∀ u, Representation ℂ G (L u)) (b : ∀ u, Representation ℂ G (K u))
  (c : ∀ u, Representation ℂ H (M u)) (d : ∀ u, Representation ℂ H (N u))
  {n m : ℕ} (p : Fin n → P) (s : Fin m → Q)

@[reducible] local instance (u : P) : AddCommGroup (L u ⊗[ℂ] M u) := inferInstance
@[reducible] local instance (u : Q) : AddCommGroup (K u ⊗[ℂ] N u) := inferInstance
@[reducible] local instance : AddCommGroup
    (TypedMixedSeparatedHom.PairedCarrier (L := L) (M := M) (K := K) (N := N) p s) := inferInstance
@[reducible] local instance : AddCommGroup
    (TypedMixedSeparatedHom.LocalCarrier (L := L) (K := K) p s) := inferInstance
@[reducible] local instance : AddCommGroup
    (TypedMixedSeparatedHom.MultiplicityCarrier (M := M) (N := N) p s) := inferInstance

abbrev raw := TypedMixedLocalHom.residual
  (TypedMixedSeparatedHom.localF (M := M) a) (TypedMixedSeparatedHom.localB (N := N) b)
  (TypedMixedSeparatedHom.residualF (L := L) c) (TypedMixedSeparatedHom.residualB (K := K) d)
  (TypedMixedSeparatedHom.commutesF a c) (TypedMixedSeparatedHom.commutesB b d) p s

def carrierEquiv : Representation.Equiv (raw a b c d p s)
    (TypedMixedSeparatedHom.residual a b c d p s) :=
  (LocalRelationNaturality.quotientEquiv
    (TypedMixedExchangeQuotient.action (TypedMixedSeparatedHom.localF (M := M) a)
      (TypedMixedSeparatedHom.localB (N := N) b) p s)
    (TypedMixedExchangeQuotient.action (TypedMixedSeparatedHom.residualF (L := L) c)
      (TypedMixedSeparatedHom.residualB (K := K) d) p s)
    (TypedMixedLocalHom.commutes _ _ _ _
      (TypedMixedSeparatedHom.commutesF a c) (TypedMixedSeparatedHom.commutesB b d) p s)
    (TypedMixedExchangeQuotient.relations p s) (TypedMixedExchangeQuotient.stable _ _ p s)
    (LocalCoinvariantTensor.action (TypedMixedSeparatedHom.localOrdered a b p s))
    (LocalCoinvariantTensor.residual (TypedMixedSeparatedHom.multiplicityOrdered c d p s))
    (LocalCoinvariantTensor.commutes _ _)
    (TypedMixedSeparatedHom.exchangeRelations c d p s)
    (TypedMixedSeparatedHom.exchange_stable c d p s)
    (TypedMixedSeparatedHom.residualEquiv c d p s)
    (TypedMixedSeparatedHom.local_compatible a b c d p s) rfl).trans
    (LocalRelationTensorNaturality.carrierEquiv
      (TypedMixedSeparatedHom.localOrdered a b p s)
      (TypedMixedSeparatedHom.multiplicityOrdered c d p s)
      (TypedMixedSeparatedHom.exchangeRelations c d p s)
      (TypedMixedSeparatedHom.exchange_stable c d p s))

omit [Fintype P] [Fintype Q] in
theorem extraction (q : MixedPatternAssembly.orderedSpace
    (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d) p s) :
    TypedMixedSeparatedHom.equiv a b c d p s q =
    (TypedMixedLocalHom.equiv _ _ _ _
      (TypedMixedSeparatedHom.commutesF a c) (TypedMixedSeparatedHom.commutesB b d) p s q).comp
      (carrierEquiv a b c d p s).symm.toIntertwiningMap := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  obtain ⟨u,rfl⟩ := (carrierEquiv a b c d p s).toLinearEquiv.surjective u
  change _ = TypedMixedLocalHom.equiv _ _ _ _ _ _ p s q
    ((carrierEquiv a b c d p s).symm (carrierEquiv a b c d p s u))
  rw [Representation.Equiv.symm_apply_apply]
  obtain ⟨u,rfl⟩ := (LocalRelationHom.image
    (TypedMixedExchangeQuotient.action (TypedMixedSeparatedHom.localF (M := M) a)
      (TypedMixedSeparatedHom.localB (N := N) b) p s)
    (TypedMixedExchangeQuotient.relations p s)).mkQ_surjective u
  obtain ⟨u,rfl⟩ := (LocalCoinvariantHom.relations
    (TypedMixedExchangeQuotient.action (TypedMixedSeparatedHom.localF (M := M) a)
      (TypedMixedSeparatedHom.localB (N := N) b) p s)).mkQ_surjective u
  change LocalCoinvariantHom.equiv _ _ _ (LocalCoinvariantTensor.commutes
    (TypedMixedSeparatedHom.localOrdered a b p s)
    (TypedMixedSeparatedHom.multiplicityOrdered c d p s))
    ((TypedMixedSeparatedHom.separateInputEquiv a b c d p s)
      ((TypedMixedLocalHom.inputEquiv _ _ _ _ _ _ p s) q)).val
      ((LocalCoinvariantTensor.residualEquiv
        (TypedMixedSeparatedHom.localOrdered a b p s)
        (TypedMixedSeparatedHom.multiplicityOrdered c d p s))
        ((LocalCoinvariantTensor.residualEquiv
          (TypedMixedSeparatedHom.localOrdered a b p s)
          (TypedMixedSeparatedHom.multiplicityOrdered c d p s)).symm
          ((LocalCoinvariantHom.relations
            (LocalCoinvariantTensor.action (TypedMixedSeparatedHom.localOrdered a b p s))).mkQ
            (TypedMixedSeparatedHom.residualEquiv c d p s u)))) = _
  rw [Representation.Equiv.apply_symm_apply]
  change (TypedMixedLocalHom.inputEquiv _ _ _ _ _ _ p s q).val.val
    ((TypedMixedSeparatedHom.residualEquiv c d p s).symm
      (TypedMixedSeparatedHom.residualEquiv c d p s u)) = _
  rw [Representation.Equiv.symm_apply_apply]
  rfl
end
end Math.TypedMixedCarrierNaturality
