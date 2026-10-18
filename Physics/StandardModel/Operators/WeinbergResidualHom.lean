import Physics.FieldTheory.Spinor.WeylPairInvariant
import Physics.StandardModel.Gauge.WeinbergWeakInvariant
import Math.RepresentationTheory.NormalizedInvariantFactor

open Math

/-! Complete residual classification in gauge/spin/flavor tensor order.
The fermion exchange condition is imposed independently, not by defining an assembly image.
Transport from actual field order is a separate obligation. -/
namespace GUT.WeinbergResidualHom
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SMEpsilonTensor
open scoped TensorProduct

def localRepresentation := external WeinbergWeakInvariant.domain
  (WeylSpinor.left.tprod WeylSpinor.left)

def localContraction := coefficient WeinbergWeakInvariant.contraction WeylSpinor.epsilonLeft

def localWitness := WeinbergWeakInvariant.witness ⊗ₜ[ℂ] WeylPairInvariant.witness

@[simp] theorem local_normalized : localContraction localWitness = 1 := by
  simp [localContraction, localWitness]

theorem local_unique (f : ExternalInvariantFactorization.Coefficient
    WeinbergWeakInvariant.domain (WeylSpinor.left.tprod WeylSpinor.left)) :
    f = f localWitness • localContraction :=
  NormalizedInvariantFactor.product_unique _ _ _ _ _ _
    WeinbergWeakInvariant.unique WeylPairInvariant.unique f

variable {R F : Type*} [Group R] [AddCommGroup F] [Module ℂ F]
  (a : Representation ℂ R F)

abbrev Coefficient := ExternalInvariantFactorization.Coefficient localRepresentation (a.tprod a)
abbrev Residual := IntertwiningMap (a.tprod a) (Representation.trivial ℂ R ℂ)

def factorEquiv : Coefficient a ≃ₗ[ℂ] Residual a :=
  NormalizedInvariantFactor.equiv _ _ localContraction localWitness local_normalized local_unique

def input (x y : Weak) (h : Fin 2 → Weak) (s t : WeylSpinor.Space) (u v : F) :=
  (((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] SymmetricPower.tprod ℂ h) ⊗ₜ[ℂ]
    (s ⊗ₜ[ℂ] t)) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] v)

theorem reconstruction (f : Coefficient a) (x y : Weak) (h : Fin 2 → Weak)
    (s t : WeylSpinor.Space) (u v : F) :
    f (input x y h s t u v) =
      WeinbergWeakInvariant.contraction ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] SymmetricPower.tprod ℂ h) *
        eps2 s t * factorEquiv a f (u ⊗ₜ[ℂ] v) :=
  NormalizedInvariantFactor.reconstruction _ _ _ _ local_normalized local_unique f _ _

/-- Exchange all parts of the two lepton fields simultaneously. -/
def HasFermionExchange (f : Coefficient a) : Prop :=
  ∀ x y h s t u v, f (input y x h t s v u) = -f (input x y h s t u v)

theorem exchange_iff (f : Coefficient a) : HasFermionExchange a f ↔
    ∀ u v, factorEquiv a f (v ⊗ₜ[ℂ] u) = factorEquiv a f (u ⊗ₜ[ℂ] v) := by
  constructor
  · intro hf u v
    have h := hf (weakBasis 0) (weakBasis 0) ![weakBasis 1,weakBasis 1]
      (weakBasis 0) (weakBasis 1) u v
    rw [reconstruction, reconstruction] at h
    norm_num [WeinbergWeakInvariant.contraction_apply, eps2, weakBasis] at h
    exact h
  · intro hf x y h s t u v
    rw [reconstruction, reconstruction, hf]
    rw [WeinbergWeakInvariant.contraction_apply, WeinbergWeakInvariant.contraction_apply]
    simp only [eps2]
    ring

def sector : Submodule ℂ (Coefficient a) where
  carrier := {f | HasFermionExchange a f}
  zero_mem' := by intro x y h s t u v; simp
  add_mem' := by
    intro f g hf hg x y h s t u v
    change f _ + g _ = -(f _ + g _)
    rw [hf, hg, neg_add]
  smul_mem' := by
    intro z f hf x y h s t u v
    change z • f _ = -(z • f _)
    rw [hf, smul_neg]

def symmetricEquiv : sector a ≃ₗ[ℂ]
    TensorSquareMultilinear.symmetricIntertwiners a (Representation.trivial ℂ R ℂ) where
  toFun f := ⟨factorEquiv a f.val, (exchange_iff a f.val).mp f.property⟩
  invFun f := ⟨(factorEquiv a).symm f.val, (exchange_iff a _).mpr (by
    intro u v
    simpa only [LinearEquiv.apply_symm_apply] using f.property u v)⟩
  left_inv f := by apply Subtype.ext; exact (factorEquiv a).symm_apply_apply f.val
  right_inv f := by apply Subtype.ext; exact (factorEquiv a).apply_symm_apply f.val
  map_add' f g := by apply Subtype.ext; exact (factorEquiv a).map_add f.val g.val
  map_smul' z f := by apply Subtype.ext; exact (factorEquiv a).map_smul z f.val

/-- The residual symmetry follows from fermion exchange and the antisymmetric spinor factor. -/
def homEquiv : sector a ≃ₗ[ℂ]
    IntertwiningMap (a.symmetricPower 2) (Representation.trivial ℂ R ℂ) :=
  (symmetricEquiv a).trans (TensorSquareMultilinear.symmetricSquareEquiv a _)

theorem exists_nonzero_iff : (∃ f : sector a, f ≠ 0) ↔
    ∃ k : IntertwiningMap (a.symmetricPower 2) (Representation.trivial ℂ R ℂ), k ≠ 0 := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨homEquiv a f, fun h => hf ((homEquiv a).injective (h.trans (map_zero _).symm))⟩
  · rintro ⟨k, hk⟩
    exact ⟨(homEquiv a).symm k, fun h =>
      hk ((homEquiv a).symm.injective (h.trans (map_zero _).symm))⟩

theorem eq_zero_of_subsingleton [Subsingleton F] (f : sector a) : f = 0 := by
  apply (symmetricEquiv a).injective
  apply Subtype.ext
  apply IntertwiningMap.ext
  apply TensorProduct.ext'
  intro u v
  have hu : u = 0 := Subsingleton.elim _ _
  simp [hu]

end
end GUT.WeinbergResidualHom
