import Math.RepresentationTheory.FiniteInvariantFactor
import Math.LinearAlgebra.StatisticalCompleteness

/-! A finite local invariant basis induces explicit exchange matrices on
residual coefficients. Flavor need not be finite-dimensional. Exchanges commute
with the relevant group actions because they are representation equivalences.
Only generator equations are needed; no Schur decomposition is assumed. -/
namespace Math.FiniteStatisticalFactor
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor ExternalInvariantFactorization
open scoped TensorProduct
variable {G H A X I J : Type*} [Group G] [Group H] [Fintype I] [DecidableEq I]
  [AddCommMonoid A] [Module ℂ A] [AddCommMonoid X] [Module ℂ X]
  (a : Representation ℂ G A) (x : Representation ℂ H X)
  (p : I → IntertwiningMap a (Representation.trivial ℂ G ℂ)) (v : I → A)
  (hv : ∀ i j, p i (v j) = if i = j then 1 else 0)
  (hp : ∀ f : IntertwiningMap a (Representation.trivial ℂ G ℂ),
    f = ∑ i, f (v i) • p i)
  (localExchange : J → Representation.Equiv a a)
  (flavorExchange : J → Representation.Equiv x x)

abbrev Coordinates := I → IntertwiningMap x (Representation.trivial ℂ H ℂ)

/-- Pullback on full local/flavor inputs. This fixes the forward-pullback
convention; it is not claimed to be a left group action. -/
def sourceAction (j : J) : Coefficient a x →ₗ[ℂ] Coefficient a x where
  toFun f := f.comp (externalEquiv (localExchange j) (flavorExchange j)).toIntertwiningMap
  map_add' f g := by ext z; rfl
  map_smul' z f := by ext w; rfl

/-- Matrix entries are computed from local contractions and probes, not
defined by conjugating the full coordinate equivalence. -/
def matrix (j : J) (i m : I) : ℂ := p m (localExchange j (v i))

def targetAction (j : J) : Coordinates (I := I) x →ₗ[ℂ] Coordinates (I := I) x where
  toFun c i := ∑ m, matrix a p v localExchange j i m •
    ((c m).comp (flavorExchange j).toIntertwiningMap)
  map_add' c d := by
    funext i
    ext w
    simp [IntertwiningMap.sum_apply, mul_add, Finset.sum_add_distrib]
  map_smul' z c := by
    funext i
    ext w
    simp [IntertwiningMap.sum_apply, Finset.mul_sum, mul_left_comm]

theorem compatible (j : J) (f : Coefficient a x) :
    FiniteInvariantFactor.equiv a x p v hv hp
      (sourceAction a x localExchange flavorExchange j f) =
    targetAction a x p v localExchange flavorExchange j
      (FiniteInvariantFactor.equiv a x p v hv hp f) := by
  funext i
  ext w
  change f (localExchange j (v i) ⊗ₜ[ℂ] flavorExchange j w) = _
  rw [FiniteInvariantFactor.reconstruction a x p v hp f]
  simp [targetAction, matrix, FiniteInvariantFactor.equiv,
    FiniteInvariantFactor.assemble_apply, rightSlice, IntertwiningMap.sum_apply, hv]

/-- Full generator-statistics completeness with explicit local exchange
matrices and arbitrary residual group and flavor multiplicity. -/
def equiv (sign : J → ℂ) :
    StatisticalCompleteness.sector (sourceAction a x localExchange flavorExchange) sign ≃ₗ[ℂ]
      StatisticalCompleteness.sector (targetAction a x p v localExchange flavorExchange) sign :=
  StatisticalCompleteness.equiv (FiniteInvariantFactor.equiv a x p v hv hp)
    _ _ sign (compatible a x p v hv hp localExchange flavorExchange)

end
end Math.FiniteStatisticalFactor
