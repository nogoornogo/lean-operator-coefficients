/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RepresentationTheory.Basic

/-!
# Namespaced Physlib symmetric derivations

Adapted from sections D/E of PhyslibAlpha.Mathematics.SymmetricAlgebra,
revision 5bbbb30d08b8e151406a10affbc8a369b74b32c6.
The derivation and representation proofs are retained under
`Math.PhyslibSymmetric`; the upstream functoriality/product sections are omitted
because their root names conflict with TauCeti. The installed dependency is
unchanged. This module has the same semiring/module hypotheses as the fragment.
-/

namespace Math.PhyslibSymmetric

namespace SymmetricAlgebra

open _root_.SymmetricAlgebra

section Derivation

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] (d : M →ₗ[R] M)

/-- The lift of the derivation extending `d` to the trivial square-zero extension of the
  symmetric algebra: the algebra homomorphism `x ↦ (x, derivationOfLinear d x)`. -/
noncomputable def derivationHom :
    SymmetricAlgebra R M →ₐ[R]
      TrivSqZeroExt (SymmetricAlgebra R M) (SymmetricAlgebra R M) :=
  lift
    { toFun := fun x => (ι R M x, ι R M (d x))
      map_add' := fun x y => by simp only [map_add]; rfl
      map_smul' := fun c x => by simp only [map_smul, RingHom.id_apply]; rfl }

@[simp]
lemma derivationHom_ι (x : M) :
    derivationHom d (ι R M x) = (ι R M x, ι R M (d x)) :=
  lift_ι_apply _ x

/-- The first component of the square-zero lift is the identity. -/
@[simp]
lemma derivationHom_fst (x : SymmetricAlgebra R M) : (derivationHom d x).fst = x := by
  have h : (TrivSqZeroExt.fstHom R (SymmetricAlgebra R M) (SymmetricAlgebra R M)).comp
      (derivationHom d) = AlgHom.id R (SymmetricAlgebra R M) :=
    algHom_ext (LinearMap.ext fun x => by simp; rfl)
  exact DFunLike.congr_fun h x

/-- **The derivation of the symmetric algebra extending a linear endomorphism** `d` of `M`:
  the map obeying the Leibniz rule whose value on a generator `ι x` is `ι (d x)`. -/
noncomputable def derivationOfLinear : SymmetricAlgebra R M →ₗ[R] SymmetricAlgebra R M where
  toFun x := (derivationHom d x).snd
  map_add' x y := congrArg TrivSqZeroExt.snd (map_add (derivationHom d) x y)
  map_smul' c x := congrArg TrivSqZeroExt.snd (map_smul (derivationHom d) c x)

@[simp]
lemma derivationOfLinear_ι (x : M) :
    derivationOfLinear d (ι R M x) = ι R M (d x) := by
  rw [show derivationOfLinear d (ι R M x) = (derivationHom d (ι R M x)).snd from rfl,
    derivationHom_ι]
  rfl

@[simp]
lemma derivationOfLinear_one : derivationOfLinear d (1 : SymmetricAlgebra R M) = 0 :=
  congrArg TrivSqZeroExt.snd (map_one (derivationHom d))

@[simp]
lemma derivationOfLinear_algebraMap (r : R) :
    derivationOfLinear d (algebraMap R (SymmetricAlgebra R M) r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, derivationOfLinear_one, smul_zero]

/-- The Leibniz rule for the derivation extending `d`. -/
lemma derivationOfLinear_mul (x y : SymmetricAlgebra R M) :
    derivationOfLinear d (x * y)
      = derivationOfLinear d x * y + x * derivationOfLinear d y := by
  have h : derivationOfLinear d (x * y) =
      (derivationHom d x).fst * derivationOfLinear d y
        + derivationOfLinear d x * (derivationHom d y).fst :=
    congrArg TrivSqZeroExt.snd (map_mul (derivationHom d) x y)
  rw [derivationHom_fst, derivationHom_fst] at h
  exact h.trans (add_comm _ _)

/-- Derivations extending commuting endomorphisms commute. -/
lemma derivationOfLinear_comm_apply {d₁ d₂ : M →ₗ[R] M} (h : d₁ ∘ₗ d₂ = d₂ ∘ₗ d₁)
    (x : SymmetricAlgebra R M) :
    derivationOfLinear d₁ (derivationOfLinear d₂ x)
      = derivationOfLinear d₂ (derivationOfLinear d₁ x) := by
  induction x using SymmetricAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
    simp only [derivationOfLinear_ι]
    exact congrArg (ι R M) (DFunLike.congr_fun h v)
  | mul x y hx hy =>
    simp only [derivationOfLinear_mul, map_add, hx, hy]
    exact add_add_add_comm _ _ _ _
  | add x y hx hy => simp only [map_add, hx, hy]

/-- An algebra map carries one derivation to the other when the linear map it is
  determined by on the generators intertwines the two endomorphisms. The hypotheses are
  stated pointwise so that the lemma can be applied without rewriting inside a large
  algebra. -/
lemma algHom_derivationOfLinear
    (F : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R N) {f : M →ₗ[R] N}
    (hF : ∀ x, F (ι R M x) = ι R N (f x)) {d : M →ₗ[R] M} {d' : N →ₗ[R] N}
    (h : ∀ x, f (d x) = d' (f x)) (y : SymmetricAlgebra R M) :
    F (derivationOfLinear d y) = derivationOfLinear d' (F y) := by
  induction y using SymmetricAlgebra.induction with
  | algebraMap r =>
    rw [derivationOfLinear_algebraMap, map_zero, AlgHom.commutes,
      derivationOfLinear_algebraMap]
  | ι v => rw [derivationOfLinear_ι, hF, hF, derivationOfLinear_ι, h]
  | mul a b ha hb =>
    simp only [derivationOfLinear_mul, map_add, map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

end Derivation

end SymmetricAlgebra

/-!

## E. The representation extending a representation on the generators

-/

namespace Representation

variable {R G M : Type*} [CommSemiring R] [Monoid G] [AddCommMonoid M] [Module R M]

/-- The representation on the symmetric algebra extending a representation on the
  generators: the substitution homomorphism determined by the action on the generators.
  It is built from `SymmetricAlgebra.lift` rather than from `SymmetricAlgebra.map`, so that
  it is available over a commutative semiring and an additive commutative monoid — the
  generality the generator spaces of a multi-species field theory, which are direct sums,
  are elaborated at. -/
noncomputable def symmetricAlgebra (ρ : Representation R G M) :
    Representation R G (SymmetricAlgebra R M) where
  toFun g := (SymmetricAlgebra.lift (SymmetricAlgebra.ι R M ∘ₗ ρ g)).toLinearMap
  map_one' := by
    have h : SymmetricAlgebra.lift (SymmetricAlgebra.ι R M ∘ₗ ρ 1)
        = AlgHom.id R (SymmetricAlgebra R M) :=
      SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => by simp)
    rw [h]
    rfl
  map_mul' g h := by
    have hlift : SymmetricAlgebra.lift (SymmetricAlgebra.ι R M ∘ₗ ρ (g * h))
        = (SymmetricAlgebra.lift (SymmetricAlgebra.ι R M ∘ₗ ρ g)).comp
          (SymmetricAlgebra.lift (SymmetricAlgebra.ι R M ∘ₗ ρ h)) :=
      SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => by
        simp [SymmetricAlgebra.lift_ι_apply, Module.End.mul_apply])
    rw [hlift]
    rfl

/-- The action of a group element, as an algebra homomorphism. -/
noncomputable def symmetricAlgebraAlgHom (ρ : Representation R G M) (g : G) :
    SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R M :=
  SymmetricAlgebra.lift (SymmetricAlgebra.ι R M ∘ₗ ρ g)

lemma symmetricAlgebra_apply (ρ : Representation R G M) (g : G)
    (x : SymmetricAlgebra R M) :
    (Math.PhyslibSymmetric.Representation.symmetricAlgebra ρ) g x = (Math.PhyslibSymmetric.Representation.symmetricAlgebraAlgHom ρ) g x := rfl

@[simp]
lemma symmetricAlgebra_ι (ρ : Representation R G M) (g : G) (x : M) :
    (Math.PhyslibSymmetric.Representation.symmetricAlgebra ρ) g (SymmetricAlgebra.ι R M x)
      = SymmetricAlgebra.ι R M (ρ g x) :=
  (SymmetricAlgebra.lift_ι_apply _ x).trans rfl

@[simp]
lemma symmetricAlgebra_apply_one (ρ : Representation R G M) (g : G) :
    (Math.PhyslibSymmetric.Representation.symmetricAlgebra ρ) g (1 : SymmetricAlgebra R M) = 1 :=
  map_one ((Math.PhyslibSymmetric.Representation.symmetricAlgebraAlgHom ρ) g)

lemma symmetricAlgebra_apply_mul (ρ : Representation R G M) (g : G)
    (x y : SymmetricAlgebra R M) :
    (Math.PhyslibSymmetric.Representation.symmetricAlgebra ρ) g (x * y)
      = (Math.PhyslibSymmetric.Representation.symmetricAlgebra ρ) g x * (Math.PhyslibSymmetric.Representation.symmetricAlgebra ρ) g y :=
  map_mul ((Math.PhyslibSymmetric.Representation.symmetricAlgebraAlgHom ρ) g) x y

lemma symmetricAlgebra_algebraMap (ρ : Representation R G M) (g : G) (r : R) :
    (Math.PhyslibSymmetric.Representation.symmetricAlgebra ρ) g (algebraMap R (SymmetricAlgebra R M) r)
      = algebraMap R (SymmetricAlgebra R M) r :=
  AlgHom.commutes ((Math.PhyslibSymmetric.Representation.symmetricAlgebraAlgHom ρ) g) r

end Representation

namespace SymmetricAlgebra

open _root_.SymmetricAlgebra

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Covariance of the derivation under the representation. If the representation
  carries each endomorphism of a family into a combination of the others on the generators,
  then it carries the derivation extending one into the same combination of the derivations
  extending the others on the whole exterior algebra. This is the shape the statement that
  the total derivative is a Lorentz vector takes; it is proved by induction rather than by
  algebra-map extensionality, a derivation not being an algebra map. -/
lemma symmetricAlgebra_derivationOfLinear {G κ : Type*} [Monoid G] [Fintype κ]
    (ρ : Representation R G M) (g : G) (d : κ → M →ₗ[R] M) (μ : κ) (c : κ → R)
    (h : ∀ x, ρ g (d μ x) = ∑ a, c a • d a (ρ g x)) (y : SymmetricAlgebra R M) :
    (Math.PhyslibSymmetric.Representation.symmetricAlgebra ρ) g (derivationOfLinear (d μ) y)
      = ∑ a, c a • derivationOfLinear (d a) ((Math.PhyslibSymmetric.Representation.symmetricAlgebra ρ) g y) := by
  induction y using SymmetricAlgebra.induction with
  | algebraMap r =>
    rw [derivationOfLinear_algebraMap, map_zero, Representation.symmetricAlgebra_algebraMap]
    exact ((Finset.sum_congr rfl fun a _ => by
      rw [derivationOfLinear_algebraMap, smul_zero]).trans Finset.sum_const_zero).symm
  | ι v =>
    rw [derivationOfLinear_ι, Representation.symmetricAlgebra_ι,
      Representation.symmetricAlgebra_ι, h, map_sum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [map_smul, derivationOfLinear_ι]
  | mul a b ha hb =>
    rw [derivationOfLinear_mul, map_add]
    simp only [Representation.symmetricAlgebra_apply_mul]
    rw [ha, hb, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      rw [derivationOfLinear_mul, smul_add, smul_mul_assoc, mul_smul_comm]
  | add a b ha hb =>
    rw [map_add, map_add, map_add, ha, hb, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [map_add, smul_add]

/-- An algebra map carries one representation to the other when the linear map it is
  determined by on the generators intertwines the two representations on them. Unlike the
  derivation statement this is pure extensionality of algebra maps, each group element
  acting by one; the hypotheses are stated pointwise so that the lemma can be applied
  without rewriting inside a large algebra. -/
lemma algHom_symmetricAlgebra {N G : Type*} [AddCommMonoid N] [Module R N] [Monoid G]
    (F : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R N) {f : M →ₗ[R] N}
    (hF : ∀ x, F (ι R M x) = ι R N (f x))
    {ρ : Representation R G M} {σ : Representation R G N} (g : G)
    (h : ∀ x, f (ρ g x) = σ g (f x)) (y : SymmetricAlgebra R M) :
    F ((Math.PhyslibSymmetric.Representation.symmetricAlgebra ρ) g y) = (Math.PhyslibSymmetric.Representation.symmetricAlgebra σ) g (F y) := by
  have key : F.comp ((Math.PhyslibSymmetric.Representation.symmetricAlgebraAlgHom ρ) g)
      = ((Math.PhyslibSymmetric.Representation.symmetricAlgebraAlgHom σ) g).comp F :=
    SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => by
      show F ((Math.PhyslibSymmetric.Representation.symmetricAlgebraAlgHom ρ) g (ι R M x))
        = (Math.PhyslibSymmetric.Representation.symmetricAlgebraAlgHom σ) g (F (ι R M x))
      rw [show (Math.PhyslibSymmetric.Representation.symmetricAlgebraAlgHom ρ) g (ι R M x) = ι R M (ρ g x) from
          Representation.symmetricAlgebra_ι ρ g x, hF, hF,
        show (Math.PhyslibSymmetric.Representation.symmetricAlgebraAlgHom σ) g (ι R N (f x)) = ι R N (σ g (f x)) from
          Representation.symmetricAlgebra_ι σ g (f x), h])
  exact DFunLike.congr_fun key y

end SymmetricAlgebra

end Math.PhyslibSymmetric
