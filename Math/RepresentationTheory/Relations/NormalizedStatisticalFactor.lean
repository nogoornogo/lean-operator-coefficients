import Math.RepresentationTheory.Invariants.NormalizedInvariantFactor
import Math.RepresentationTheory.Relations.FiniteStatisticalFactor

/-! A normalized local invariant line transfers its exchange scalar to the
residual coefficient. In particular, two fermionic minus signs can produce
symmetric flavor coefficients. No dimension hypothesis is needed. -/
namespace Math.NormalizedStatisticalFactor
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantFactorization
open scoped TensorProduct
variable {G H A X J : Type*} [Group G] [Group H]
  [AddCommMonoid A] [Module ℂ A] [AddCommMonoid X] [Module ℂ X]
  (a : Representation ℂ G A) (x : Representation ℂ H X)
  (p : IntertwiningMap a (Representation.trivial ℂ G ℂ)) (v : A)
  (hv : p v = 1)
  (hp : ∀ f : IntertwiningMap a (Representation.trivial ℂ G ℂ), f = f v • p)
  (localExchange : J → Representation.Equiv a a)
  (flavorExchange : J → Representation.Equiv x x)

def targetAction (j : J) :
    IntertwiningMap x (Representation.trivial ℂ H ℂ) →ₗ[ℂ]
      IntertwiningMap x (Representation.trivial ℂ H ℂ) where
  toFun c := p (localExchange j v) • c.comp (flavorExchange j).toIntertwiningMap
  map_add' c d := by ext w; simp [mul_add]
  map_smul' z c := by ext w; simp [mul_left_comm]

theorem compatible (j : J) (f : Coefficient a x) :
    NormalizedInvariantFactor.equiv a x p v hv hp
      (FiniteStatisticalFactor.sourceAction a x localExchange flavorExchange j f) =
    targetAction a x p v localExchange flavorExchange j
      (NormalizedInvariantFactor.equiv a x p v hv hp f) := by
  ext w
  change f (localExchange j v ⊗ₜ[ℂ] flavorExchange j w) = _
  exact NormalizedInvariantFactor.reconstruction a x p v hv hp f _ _

def equiv (sign : J → ℂ) :
    StatisticalCompleteness.sector
      (FiniteStatisticalFactor.sourceAction a x localExchange flavorExchange) sign ≃ₗ[ℂ]
    StatisticalCompleteness.sector (targetAction a x p v localExchange flavorExchange) sign :=
  StatisticalCompleteness.equiv (NormalizedInvariantFactor.equiv a x p v hv hp)
    _ _ sign (compatible a x p v hv hp localExchange flavorExchange)

end
end Math.NormalizedStatisticalFactor
