import Math.RepresentationTheory.Invariants.AutomorphismCovariantHom
import TauCeti.RepresentationTheory.ExteriorPower

/-! Exterior and supported quotient carriers for normalizing residual actions. -/
namespace Math.AutomorphismCovariantExterior
set_option autoImplicit false
noncomputable section
open Representation AutomorphismCovariantHom

variable {k G H V : Type*} [Field k] [Group G] [Group H]
  [AddCommGroup V] [Module k V]
  (a : Representation k G V) (alpha : H →* MulAut G) (A : Action a alpha)

/-- Covariance on fields induces covariance on their actual exterior powers. -/
def exteriorAction (n : ℕ) : Action (a.exteriorPower n) alpha where
  residual := A.residual.exteriorPower n
  covariance h g v := by
    have he : (A.residual.exteriorPower n h).comp (a.exteriorPower n g) =
        (a.exteriorPower n (alpha h g)).comp (A.residual.exteriorPower n h) := by
      apply exteriorPower.linearMap_ext
      ext w
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, Representation.exteriorPower_apply_ιMulti]
      have hh : (A.residual h) ∘ (a g) ∘ w =
          (a (alpha h g)) ∘ (A.residual h) ∘ w := by
        funext i
        exact A.covariance h g (w i)
      rw [hh]
    exact congrArg (fun f => f v) he

/-- An independently specified unsupported-input span must be stable under
both actions. These certificates are checked separately from Hom completeness. -/
structure Support (n : ℕ) where
  unsupported : Submodule k (⋀[k]^n V)
  local_stable : ∀ g, unsupported ≤ unsupported.comap (a.exteriorPower n g)
  residual_stable : ∀ h, unsupported ≤ unsupported.comap (A.residual.exteriorPower n h)

/-- Build the unsupported span from explicit pure inputs, deriving stability
from preservation of the independently specified generator set. -/
def ofGenerators (n : ℕ) (inputs : Set (Fin n → V))
    (hl : ∀ g v, v ∈ inputs → (fun i => a g (v i)) ∈ inputs)
    (hr : ∀ h v, v ∈ inputs → (fun i => A.residual h (v i)) ∈ inputs) :
    Support a alpha A n where
  unsupported := RelationQuotient.relations (k := k)
    (fun v : inputs => exteriorPower.ιMulti k n v.val)
  local_stable := by
    apply RelationQuotient.relations_stable
    intro g v
    rw [Representation.exteriorPower_apply_ιMulti]
    exact Submodule.subset_span ⟨⟨_, hl g v.val v.property⟩, rfl⟩
  residual_stable := by
    apply RelationQuotient.relations_stable
    intro h v
    rw [Representation.exteriorPower_apply_ιMulti]
    exact Submodule.subset_span ⟨⟨_, hr h v.val v.property⟩, rfl⟩

variable {n : ℕ} (S : Support a alpha A n)

abbrev localQuotient := (a.exteriorPower n).quotient S.unsupported S.local_stable

/-- Normalization descends through the support quotient without commutation. -/
def supportedAction : Action (localQuotient a alpha A S) alpha where
  residual := (A.residual.exteriorPower n).quotient S.unsupported S.residual_stable
  covariance h g v := by
    obtain ⟨w, rfl⟩ := S.unsupported.mkQ_surjective v
    exact congrArg S.unsupported.mkQ ((exteriorAction a alpha A n).covariance h g w)

/-- Supported invariant functionals defined on the original exterior carrier. -/
def Input : Submodule k (LocalCoinvariantHom.invariantHom (a.exteriorPower n)
    (A.residual.exteriorPower n) (trivial k H k)) where
  carrier := {f | S.unsupported ≤ LinearMap.ker f.val.toLinearMap}
  zero_mem' := by intro v hv; rfl
  add_mem' := by
    intro f q hf hq v hv
    change f.val.toLinearMap v + q.val.toLinearMap v = 0
    rw [hf hv, hq hv, add_zero]
  smul_mem' := by
    intro c f hf v hv
    change c • f.val.toLinearMap v = 0
    rw [hf hv, smul_zero]

set_option maxHeartbeats 800000 in
/-- Support descent and pullback are inverse on independently defined inputs. -/
def supportEquiv : Input a alpha A S ≃ₗ[k]
    LocalCoinvariantHom.invariantHom (localQuotient a alpha A S)
      (supportedAction a alpha A S).residual (trivial k H k) where
  toFun f := ⟨RelationQuotient.descend (A.residual.exteriorPower n) (trivial k H k)
    S.unsupported S.residual_stable ⟨f.val.val, f.property⟩, by
      intro g v
      obtain ⟨w, rfl⟩ := S.unsupported.mkQ_surjective v
      exact f.val.property g w⟩
  invFun f := ⟨⟨f.val.comp (RelationQuotient.projection (A.residual.exteriorPower n)
    S.unsupported S.residual_stable), by
      intro g v
      exact f.property g (S.unsupported.mkQ v)⟩, by
        intro v hv
        change f.val (S.unsupported.mkQ v) = 0
        have hz : S.unsupported.mkQ v = 0 :=
          (Submodule.Quotient.mk_eq_zero S.unsupported).mpr hv
        rw [hz, map_zero]⟩
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    rfl
  right_inv f := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := S.unsupported.mkQ_surjective v
    rfl
  map_add' f q := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := S.unsupported.mkQ_surjective v
    rfl
  map_smul' c f := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := S.unsupported.mkQ_surjective v
    rfl

/-- The supported coefficients are defined independently as invariant maps on
an actual support quotient, then identified with residual Hom. -/
def equiv : LocalCoinvariantHom.invariantHom (localQuotient a alpha A S)
    (supportedAction a alpha A S).residual (trivial k H k) ≃ₗ[k]
    IntertwiningMap (AutomorphismCovariantHom.quotient (localQuotient a alpha A S)
      alpha (supportedAction a alpha A S)) (trivial k H k) :=
  AutomorphismCovariantHom.equiv _ alpha (supportedAction a alpha A S) (trivial k H k)

theorem forbidden_iff :
    (∀ f : LocalCoinvariantHom.invariantHom (localQuotient a alpha A S)
      (supportedAction a alpha A S).residual (trivial k H k), f = 0) ↔
    ∀ q : IntertwiningMap (AutomorphismCovariantHom.quotient (localQuotient a alpha A S)
      alpha (supportedAction a alpha A S)) (trivial k H k), q = 0 :=
  AutomorphismCovariantHom.forbidden_iff _ alpha (supportedAction a alpha A S) (trivial k H k)

/-- Full extraction/reconstruction from supported original exterior functionals. -/
def inputEquiv := (supportEquiv a alpha A S).trans (equiv a alpha A S)

theorem input_forbidden_iff :
    (∀ f : Input a alpha A S, f = 0) ↔
    ∀ q : IntertwiningMap (AutomorphismCovariantHom.quotient (localQuotient a alpha A S)
      alpha (supportedAction a alpha A S)) (trivial k H k), q = 0 := by
  let e := inputEquiv a alpha A S
  constructor
  · intro hf q
    obtain ⟨f, rfl⟩ := e.surjective q
    rw [hf f, map_zero]
  · intro hq f
    apply e.injective
    exact (hq (e f)).trans (map_zero e).symm

end
end Math.AutomorphismCovariantExterior
