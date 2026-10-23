import Math.RepresentationTheory.Tensors.ExternalInvariantTensor
import Math.LinearAlgebra.Selection.StatisticalCompleteness

/-! Transport entire invariant coefficient spaces, including descent through
a surjective group map. -/
namespace Math.InvariantCoefficientTransport
set_option autoImplicit false
noncomputable section
open Representation

variable {G K A B : Type*} [Group G] [Group K]
  [AddCommMonoid A] [Module ℂ A] [AddCommMonoid B] [Module ℂ B]

abbrev Invariants (a : Representation ℂ G A) :=
  IntertwiningMap a (Representation.trivial ℂ G ℂ)

def alongEquiv {a : Representation ℂ G A} {b : Representation ℂ G B}
    (e : Representation.Equiv a b) : Invariants a ≃ₗ[ℂ] Invariants b where
  toFun f := f.comp e.symm.toIntertwiningMap
  invFun f := f.comp e.toIntertwiningMap
  left_inv f := by ext v; exact congrArg f (e.toLinearEquiv.symm_apply_apply v)
  right_inv f := by ext v; exact congrArg f (e.toLinearEquiv.apply_symm_apply v)
  map_add' f g := by ext v; rfl
  map_smul' z f := by ext v; rfl

/-- Forward pullback on coefficient tensors. The input permutation itself is
an equivariant field map, so residual and local invariance are preserved. -/
def pullbackMap {a : Representation ℂ G A} (s : IntertwiningMap a a) :
    Invariants a →ₗ[ℂ] Invariants a where
  toFun f := f.comp s
  map_add' f h := by ext v; rfl
  map_smul' z f := by ext v; rfl

def pullback {a : Representation ℂ G A} (s : Representation.Equiv a a) :
    Invariants a →ₗ[ℂ] Invariants a := pullbackMap s.toIntertwiningMap

/-- Weight/degree constraints may use noninvertible maps, for example species
scaling at zero. They obey the same transport law as permutation statistics. -/
theorem alongMaps_compatible {J : Type*}
    {a : Representation ℂ G A} {b : Representation ℂ G B}
    (e : Representation.Equiv a b) (s : J → IntertwiningMap a a)
    (t : J → IntertwiningMap b b)
    (commutes : ∀ j v, e (s j v) = t j (e v)) (j : J) (f : Invariants a) :
    alongEquiv e (pullbackMap (s j) f) = pullbackMap (t j) (alongEquiv e f) := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  change f (s j (e.symm v)) = f (e.symm (t j v))
  apply congrArg f
  apply e.injective
  change e (s j (e.symm v)) = e (e.symm (t j v))
  calc
    _ = t j (e (e.symm v)) := commutes j _
    _ = t j v := congrArg (t j) (e.toLinearEquiv.apply_symm_apply v)
    _ = _ := (e.toLinearEquiv.apply_symm_apply (t j v)).symm

def alongConstraints {J : Type*}
    {a : Representation ℂ G A} {b : Representation ℂ G B}
    (e : Representation.Equiv a b) (s : J → IntertwiningMap a a)
    (t : J → IntertwiningMap b b)
    (commutes : ∀ j v, e (s j v) = t j (e v)) (weight : J → ℂ) :
    StatisticalCompleteness.sector (fun j => pullbackMap (s j)) weight ≃ₗ[ℂ]
      StatisticalCompleteness.sector (fun j => pullbackMap (t j)) weight :=
  StatisticalCompleteness.equiv (alongEquiv e) _ _ weight
    (alongMaps_compatible e s t commutes)

/-- The only extra certificate for actual-field statistics is commutation of
field maps. No coefficient, spanning or nonzero premise is supplied. -/
theorem alongEquiv_compatible {J : Type*}
    {a : Representation ℂ G A} {b : Representation ℂ G B}
    (e : Representation.Equiv a b) (s : J → Representation.Equiv a a)
    (t : J → Representation.Equiv b b)
    (commutes : ∀ j v, e (s j v) = t j (e v)) (j : J) (f : Invariants a) :
    alongEquiv e (pullback (s j) f) = pullback (t j) (alongEquiv e f) := by
  exact alongMaps_compatible e (fun j => (s j).toIntertwiningMap)
    (fun j => (t j).toIntertwiningMap) commutes j f

def alongStatistics {J : Type*}
    {a : Representation ℂ G A} {b : Representation ℂ G B}
    (e : Representation.Equiv a b) (s : J → Representation.Equiv a a)
    (t : J → Representation.Equiv b b)
    (commutes : ∀ j v, e (s j v) = t j (e v)) (sign : J → ℂ) :
    StatisticalCompleteness.sector (fun j => pullback (s j)) sign ≃ₗ[ℂ]
      StatisticalCompleteness.sector (fun j => pullback (t j)) sign :=
  StatisticalCompleteness.equiv (alongEquiv e) _ _ sign
    (alongEquiv_compatible e s t commutes)

def alongSurjection (a : Representation ℂ K A) (j : G →* K)
    (hj : Function.Surjective j) : Invariants (a.comp j) ≃ₗ[ℂ] Invariants a where
  toFun f := {
    toLinearMap := f.toLinearMap
    isIntertwining' k := by
      obtain ⟨g, rfl⟩ := hj k
      exact f.isIntertwining' g }
  invFun f := {
    toLinearMap := f.toLinearMap
    isIntertwining' g := f.isIntertwining' (j g) }
  left_inv f := by ext v; rfl
  right_inv f := by ext v; rfl
  map_add' f g := by ext v; rfl
  map_smul' z f := by ext v; rfl

end
end Math.InvariantCoefficientTransport
