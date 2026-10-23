import Math.RepresentationTheory.Coefficients.InvariantCoefficientTransport
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Equivariant Hom descent through an independently specified stable relation
module. No dimension, topology, compactness or semisimplicity is required. -/
namespace Math.RelationQuotient
set_option autoImplicit false
noncomputable section
open Representation

variable {k H U W : Type*} [Field k] [Group H]
  [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
  (rho : Representation k H U) (tau : Representation k H W)
  (R : Submodule k U) (stable : ∀ g, R ≤ R.comap (rho g))

def vanishing : Submodule k (IntertwiningMap rho tau) where
  carrier := {f | R ≤ LinearMap.ker f.toLinearMap}
  zero_mem' := by intro u hu; rfl
  add_mem' := by
    intro f h hf hh u hu
    change f.toLinearMap u + h.toLinearMap u = 0
    rw [hf hu, hh hu, add_zero]
  smul_mem' := by
    intro z f hf u hu
    change z • f.toLinearMap u = 0
    rw [hf hu, smul_zero]

/-- Change equal representation presentations without changing the functional. -/
def congr {rho' : Representation k H U} {tau' : Representation k H W}
    (hr : rho = rho') (ht : tau = tau') : vanishing rho tau R ≃ₗ[k] vanishing rho' tau' R := by
  subst rho'
  subst tau'
  exact LinearEquiv.refl k _

theorem congr_apply {rho' : Representation k H U} {tau' : Representation k H W}
    (hr : rho = rho') (ht : tau = tau') (f : vanishing rho tau R) (u : U) :
    (congr rho tau R hr ht f).val u = f.val u := by
  subst rho'
  subst tau'
  rfl

section Transport
variable {U' : Type*} [AddCommGroup U'] [Module k U']
  {rho' : Representation k H U'} (e : Representation.Equiv rho rho')

include stable in
theorem map_stable : ∀ h, R.map e.toLinearMap ≤ (R.map e.toLinearMap).comap (rho' h) := by
  intro h u hu
  obtain ⟨v, hv, rfl⟩ := hu
  refine ⟨rho h v, stable h hv, ?_⟩
  exact IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap h v

def alongEquiv : vanishing rho tau R ≃ₗ[k] vanishing rho' tau (R.map e.toLinearMap) where
  toFun f := ⟨f.val.comp e.symm.toIntertwiningMap, by
    rintro _ ⟨u, hu, rfl⟩
    change f.val.toLinearMap (e.toLinearEquiv.symm (e.toLinearEquiv u)) = 0
    rw [e.toLinearEquiv.symm_apply_apply]
    exact f.property hu⟩
  invFun f := ⟨f.val.comp e.toIntertwiningMap, by
    intro u hu
    exact f.property ⟨u, hu, rfl⟩⟩
  left_inv f := by
    apply Subtype.ext
    ext u
    exact congrArg f.val (e.toLinearEquiv.symm_apply_apply u)
  right_inv f := by
    apply Subtype.ext
    ext u
    exact congrArg f.val (e.toLinearEquiv.apply_symm_apply u)
  map_add' f q := by apply Subtype.ext; ext u; rfl
  map_smul' z f := by apply Subtype.ext; ext u; rfl

theorem alongEquiv_apply (f : vanishing rho tau R) (u : U) :
    (alongEquiv rho tau R e f).val (e u) = f.val u := by
  change f.val (e.toLinearEquiv.symm (e.toLinearEquiv u)) = f.val u
  rw [e.toLinearEquiv.symm_apply_apply]
end Transport

def projection : IntertwiningMap rho (rho.quotient R stable) where
  toLinearMap := R.mkQ
  isIntertwining' g := by ext u; rfl

def descend (f : vanishing rho tau R) :
    IntertwiningMap (rho.quotient R stable) tau where
  toLinearMap := R.liftQ f.val.toLinearMap f.property
  isIntertwining' g := by
    apply LinearMap.ext
    intro u
    obtain ⟨v, rfl⟩ := R.mkQ_surjective u
    exact IntertwiningMap.isIntertwining _ _ f.val g v

def pull (f : IntertwiningMap (rho.quotient R stable) tau) : vanishing rho tau R :=
  ⟨f.comp (projection rho R stable), by
    intro u hu
    change f (R.mkQ u) = 0
    have hz : R.mkQ u = 0 := (Submodule.Quotient.mk_eq_zero R).mpr hu
    rw [hz, map_zero]⟩

/-- Necessary and sufficient descent, with an actual quotient representation. -/
def equiv : vanishing rho tau R ≃ₗ[k]
    IntertwiningMap (rho.quotient R stable) tau where
  toFun := descend rho tau R stable
  invFun := pull rho tau R stable
  left_inv f := by apply Subtype.ext; ext u; rfl
  right_inv f := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro u
    obtain ⟨v, rfl⟩ := R.mkQ_surjective u
    rfl
  map_add' f h := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro u
    obtain ⟨v, rfl⟩ := R.mkQ_surjective u
    rfl
  map_smul' z f := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro u
    obtain ⟨v, rfl⟩ := R.mkQ_surjective u
    rfl

@[simp] theorem equiv_mk (f : vanishing rho tau R) (u : U) :
    equiv rho tau R stable f (R.mkQ u) = f.val u := rfl

@[simp] theorem equiv_symm_apply
    (f : IntertwiningMap (rho.quotient R stable) tau) (u : U) :
    ((equiv rho tau R stable).symm f).val u = f (R.mkQ u) := rfl

section Generators
variable {J : Type*} (relation : J → U)

def relations : Submodule k U := Submodule.span k (Set.range relation)

theorem vanish_relations_iff (f : IntertwiningMap rho tau) :
    f ∈ vanishing rho tau (relations relation) ↔ ∀ j, f (relation j) = 0 := by
  change Submodule.span k (Set.range relation) ≤ LinearMap.ker f.toLinearMap ↔ _
  rw [Submodule.span_le]
  constructor
  · intro h j; exact h ⟨j, rfl⟩
  · intro h u hu
    obtain ⟨j, rfl⟩ := hu
    exact h j

/-- Stability is checked on the generating input relations, not on all span
elements and not by assuming completeness of constrained coefficients. -/
theorem relations_stable
    (h : ∀ g j, rho g (relation j) ∈ relations (k := k) relation) :
    ∀ g, relations (k := k) relation ≤ (relations (k := k) relation).comap (rho g) := by
  intro g
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact h g j

end Generators
end
end Math.RelationQuotient
