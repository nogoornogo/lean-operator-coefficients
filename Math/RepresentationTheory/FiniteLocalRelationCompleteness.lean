import Math.RepresentationTheory.ResidualRelationPresentation

/-! Derivative-free algebraic completeness from a proved local invariant basis:
exchange-constrained full coefficients are exactly residual-equivariant maps
out of an explicitly generated input quotient. -/
namespace Math.FiniteLocalRelationCompleteness
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantFactorization
open scoped TensorProduct

variable {G H A X I J : Type*} [Group G] [Group H] [Fintype I] [DecidableEq I]
  [AddCommMonoid A] [Module ℂ A] [AddCommGroup X] [Module ℂ X]
  (a : Representation ℂ G A) (x : Representation ℂ H X)
  (p : I → IntertwiningMap a (Representation.trivial ℂ G ℂ)) (v : I → A)
  (hv : ∀ i j, p i (v j) = if i = j then 1 else 0)
  (hp : ∀ f : IntertwiningMap a (Representation.trivial ℂ G ℂ),
    f = ∑ i, f (v i) • p i)
  (localExchange : J → Representation.Equiv a a)
  (flavorExchange : J → Representation.Equiv x x) (sign : J → ℂ)

abbrev relations : Submodule ℂ (I →₀ X) :=
  ResidualRelationPresentation.relations x
    (FiniteStatisticalFactor.matrix a p v localExchange)
    (fun j => (flavorExchange j).toIntertwiningMap) sign

abbrev residualRepresentation :=
  ResidualRelationPresentation.quotientRepresentation x
    (FiniteStatisticalFactor.matrix a p v localExchange)
    (fun j => (flavorExchange j).toIntertwiningMap) sign

omit [DecidableEq I] in
theorem target_iff (c : FiniteStatisticalFactor.Coordinates (I := I) x) :
    c ∈ StatisticalCompleteness.sector
      (FiniteStatisticalFactor.targetAction a x p v localExchange flavorExchange) sign ↔
    c ∈ ResidualRelationPresentation.sector x
      (FiniteStatisticalFactor.matrix a p v localExchange)
      (fun j => (flavorExchange j).toIntertwiningMap) sign := by
  constructor
  · intro h j i w
    have he := congrArg (fun c : FiniteStatisticalFactor.Coordinates (I := I) x => c i w) (h j)
    simpa [FiniteStatisticalFactor.targetAction, IntertwiningMap.sum_apply, smul_eq_mul] using he
  · intro h j
    funext i
    ext w
    simpa [FiniteStatisticalFactor.targetAction, IntertwiningMap.sum_apply, smul_eq_mul] using h j i w

def targetEquiv : StatisticalCompleteness.sector
    (FiniteStatisticalFactor.targetAction a x p v localExchange flavorExchange) sign ≃ₗ[ℂ]
    ResidualRelationPresentation.sector x
      (FiniteStatisticalFactor.matrix a p v localExchange)
      (fun j => (flavorExchange j).toIntertwiningMap) sign :=
  (ConstrainedCompleteness.Presentation.mk (LinearEquiv.refl ℂ _)
    (target_iff a x p v localExchange flavorExchange sign)).equiv

/-- Local completeness plus independent input exchange relations gives an
actual residual-Hom quotient classification, not only a coefficient subspace. -/
def equiv : StatisticalCompleteness.sector
    (FiniteStatisticalFactor.sourceAction a x localExchange flavorExchange) sign ≃ₗ[ℂ]
    IntertwiningMap (residualRepresentation a x p v localExchange flavorExchange sign)
      (Representation.trivial ℂ H ℂ) :=
  (FiniteStatisticalFactor.equiv a x p v hv hp localExchange flavorExchange sign).trans
    ((targetEquiv a x p v localExchange flavorExchange sign).trans
      (ResidualRelationPresentation.equiv x
        (FiniteStatisticalFactor.matrix a p v localExchange)
        (fun j => (flavorExchange j).toIntertwiningMap) sign))

@[simp] theorem extraction (f : StatisticalCompleteness.sector
    (FiniteStatisticalFactor.sourceAction a x localExchange flavorExchange) sign)
    (i : I) (w : X) :
    equiv a x p v hv hp localExchange flavorExchange sign f
      ((relations a x p v localExchange flavorExchange sign).mkQ (Finsupp.single i w)) =
      f.val (v i ⊗ₜ[ℂ] w) := by
  change ResidualRelationPresentation.equiv x
    (FiniteStatisticalFactor.matrix a p v localExchange)
    (fun j => (flavorExchange j).toIntertwiningMap) sign
    (targetEquiv a x p v localExchange flavorExchange sign
      (FiniteStatisticalFactor.equiv a x p v hv hp localExchange flavorExchange sign f))
    _ = _
  rw [ResidualRelationPresentation.equiv_single]
  rfl

@[simp] theorem reconstruction
    (q : IntertwiningMap (residualRepresentation a x p v localExchange flavorExchange sign)
      (Representation.trivial ℂ H ℂ)) (u : A) (w : X) :
    ((equiv a x p v hv hp localExchange flavorExchange sign).symm q).val
      (u ⊗ₜ[ℂ] w) =
    ∑ i, p i u * q
      ((relations a x p v localExchange flavorExchange sign).mkQ (Finsupp.single i w)) := by
  exact FiniteInvariantFactor.assemble_apply a x p _ u w

include hv hp in
theorem nonzero_iff :
    (∃ f : StatisticalCompleteness.sector
      (FiniteStatisticalFactor.sourceAction a x localExchange flavorExchange) sign, f ≠ 0) ↔
    ∃ q : IntertwiningMap (residualRepresentation a x p v localExchange flavorExchange sign)
      (Representation.trivial ℂ H ℂ), q ≠ 0 :=
  ConstrainedCompleteness.exists_nonzero_iff
    (equiv a x p v hv hp localExchange flavorExchange sign)

end
end Math.FiniteLocalRelationCompleteness
