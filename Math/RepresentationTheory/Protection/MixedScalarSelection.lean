import Math.RepresentationTheory.Coefficients.GradedMixedCompleteness
import Math.RepresentationTheory.Protection.InvariantProtection

/-! Scalar action descends through local coinvariants and Bose/Fermi relations.
Neutrality is necessary, never asserted sufficient for an invariant. -/
namespace Math.MixedScalarSelection
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct BigOperators

section Scalar
variable {k H V : Type*} [Field k] [Group H] [AddCommGroup V] [Module k V]

theorem invariant_zero (r : Representation k H V) (g : H) (z : k)
    (hz : z ≠ 1) (hs : ∀ v, r g v = z • v)
    (f : IntertwiningMap r (trivial k H k)) : f = 0 := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  have h := IntertwiningMap.isIntertwining _ _ f g v
  rw [hs, map_smul] at h
  have he : (z - 1) * f v = 0 := by
    change z * f v = f v at h
    rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hz)

theorem quotient_scalar (r : Representation k H V) (R : Submodule k V)
    (stable : ∀ h, R ≤ R.comap (r h)) (g : H) (z : k)
    (hs : ∀ v, r g v = z • v) :
    ∀ v, r.quotient R stable g v = z • v := by
  intro v
  obtain ⟨v, rfl⟩ := R.mkQ_surjective v
  change R.mkQ (r g v) = z • R.mkQ v
  rw [hs, map_smul]
end Scalar

section Tensor
variable {H I : Type*} [Group H] [Fintype I]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem tensor_scalar (r : ∀ i, Representation ℂ H (V i)) (g : H) (z : I → ℂ)
    (hs : ∀ i v, r i g v = z i • v) :
    ∀ v, MultilinearInvariantHom.tensorRepresentation r g v = (∏ i, z i) • v := by
  have he : MultilinearInvariantHom.tensorRepresentation r g =
      (∏ i, z i) • LinearMap.id := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply,
      MultilinearInvariantHom.tensorRepresentation_tprod, hs,
      LinearMap.smul_apply, LinearMap.id_apply]
    exact (PiTensorProduct.tprod ℂ).map_smul_univ z v
  intro v
  exact LinearMap.congr_fun he v
end Tensor

section Mixed
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

def total (zf : P → ℂ) (zb : Q → ℂ) := (∏ i, zf (p i)) * ∏ j, zb (s j)

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem ordered_scalar (g : H) (zf : P → ℂ) (zb : Q → ℂ)
    (hf : ∀ u v, c u g v = zf u • v) (hb : ∀ u v, d u g v = zb u • v) :
    ∀ v, TypedMixedSeparatedHom.multiplicityOrdered c d p s g v = total p s zf zb • v := by
  have he : TypedMixedSeparatedHom.multiplicityOrdered c d p s g =
      total p s zf zb • LinearMap.id := by
    apply TensorProduct.ext'
    intro v w
    simp only [TypedMixedSeparatedHom.multiplicityOrdered, TypedMixedExchangeQuotient.action,
      Representation.tprod_apply, TensorProduct.map_tmul,
      tensor_scalar (fun i => c (p i)) g (fun i => zf (p i)) (fun i => hf (p i)),
      tensor_scalar (fun j => d (s j)) g (fun j => zb (s j)) (fun j => hb (s j)),
      TensorProduct.smul_tmul_smul, total, LinearMap.smul_apply, LinearMap.id_apply]
  intro v
  exact LinearMap.congr_fun he v

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem base_scalar (g : H) (zf : P → ℂ) (zb : Q → ℂ)
    (hf : ∀ u v, c u g v = zf u • v) (hb : ∀ u v, d u g v = zb u • v) :
    ∀ v, LocalRelationTensorHom.base (TypedMixedSeparatedHom.localOrdered a b p s)
      (TypedMixedSeparatedHom.multiplicityOrdered c d p s) g v = total p s zf zb • v := by
  have he : LocalRelationTensorHom.base (TypedMixedSeparatedHom.localOrdered a b p s)
      (TypedMixedSeparatedHom.multiplicityOrdered c d p s) g =
      total p s zf zb • LinearMap.id := by
    apply TensorProduct.ext'
    intro v w
    simp only [LocalRelationTensorHom.base, Representation.tprod_apply,
      TensorProduct.map_tmul, Representation.trivial_apply, ordered_scalar c d p s g zf zb hf hb,
      TensorProduct.tmul_smul, LinearMap.smul_apply, LinearMap.id_apply]
  intro v
  exact LinearMap.congr_fun he v

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem residual_scalar (g : H) (zf : P → ℂ) (zb : Q → ℂ)
    (hf : ∀ u v, c u g v = zf u • v) (hb : ∀ u v, d u g v = zb u • v) :
    ∀ v, TypedMixedSeparatedHom.residual a b c d p s g v = total p s zf zb • v :=
  quotient_scalar _ _ _ g _ (base_scalar a b c d p s g zf zb hf hb)

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem factor_zero (g : H) (zf : P → ℂ) (zb : Q → ℂ)
    (hf : ∀ u v, c u g v = zf u • v) (hb : ∀ u v, d u g v = zb u • v)
    (hne : total p s zf zb ≠ 1)
    (f : IntertwiningMap (TypedMixedSeparatedHom.residual a b c d p s) (trivial ℂ H ℂ)) : f = 0 :=
  invariant_zero _ g _ hne (residual_scalar a b c d p s g zf zb hf hb) f

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem nonzero_neutral (g : H) (zf : P → ℂ) (zb : Q → ℂ)
    (hf : ∀ u v, c u g v = zf u • v) (hb : ∀ u v, d u g v = zb u • v)
    (f : IntertwiningMap (TypedMixedSeparatedHom.residual a b c d p s) (trivial ℂ H ℂ))
    (hne : f ≠ 0) : total p s zf zb = 1 := by
  by_contra ht
  exact hne (factor_zero a b c d p s g zf zb hf hb ht f)

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
/-- A local obstruction kills coefficients even when residual charges are neutral. -/
theorem local_factor_zero (g : G) (z : ℂ) (hz : z ≠ 1)
    (hs : ∀ v, TypedMixedSeparatedHom.localOrdered a b p s g v = z • v)
    (f : IntertwiningMap (TypedMixedSeparatedHom.residual a b c d p s) (trivial ℂ H ℂ)) : f = 0 := by
  let e := LocalRelationTensorHom.equiv (TypedMixedSeparatedHom.localOrdered a b p s)
    (TypedMixedSeparatedHom.multiplicityOrdered c d p s)
    (TypedMixedSeparatedHom.exchangeRelations c d p s)
    (TypedMixedSeparatedHom.exchange_stable c d p s)
  let q := e.symm f
  apply e.symm.injective
  change q = e.symm 0
  rw [map_zero]
  apply Subtype.ext
  apply Subtype.ext
  apply IntertwiningMap.ext
  apply TensorProduct.ext'
  intro v w
  have hi := q.val.property g (v ⊗ₜ[ℂ] w)
  have hh : z • q.val.val (v ⊗ₜ[ℂ] w) = q.val.val (v ⊗ₜ[ℂ] w) := by
    simpa only [LocalCoinvariantTensor.action, Representation.tprod_apply,
      TensorProduct.map_tmul, Representation.trivial_apply, hs,
      TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul] using hi
  change q.val.val (v ⊗ₜ[ℂ] w) = 0
  have he : (z - 1) * q.val.val (v ⊗ₜ[ℂ] w) = 0 := by
    change z * q.val.val (v ⊗ₜ[ℂ] w) = q.val.val (v ⊗ₜ[ℂ] w) at hh
    rw [sub_mul, one_mul, hh, sub_self]
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hz)

variable (allowed : ∀ n m : ℕ, (Fin n → P) → (Fin m → Q) → Prop)
  [∀ n m v w, Decidable (allowed n m v w)]
  (stable : ∀ n m v w (e : Equiv.Perm (Fin n)) (f : Equiv.Perm (Fin m)),
    allowed n m (v ∘ e) (w ∘ f) ↔ allowed n m v w)

include stable in
/-- Each forbidden content can have its own detecting group element. -/
theorem all_forbidden
    (detect : ∀ n m (p : Fin n → P) (s : Fin m → Q), allowed n m p s →
      ∃ g zf zb, (∀ u v, c u g v = zf u • v) ∧ (∀ u v, d u g v = zb u • v) ∧
        total p s zf zb ≠ 1) :
    ∀ n m, ∀ f : MixedSpeciesProjection.supportSpace (allowed n m)
      (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d), f = 0 := by
  intro n m
  apply (GradedMixedCompleteness.selected_forbidden_iff a b c d n m
    (allowed n m) (stable n m)).mpr
  intro x f
  obtain ⟨g,zf,zb,hf,hb,hne⟩ := detect n m x.val.out.1 x.val.out.2 x.property
  exact factor_zero a b c d _ _ g zf zb hf hb hne f
include stable in
theorem all_hom_forbidden
    (detect : ∀ n m (p : Fin n → P) (s : Fin m → Q), allowed n m p s →
      ∃ g zf zb, (∀ u v, c u g v = zf u • v) ∧ (∀ u v, d u g v = zb u • v) ∧
        total p s zf zb ≠ 1) :
    ∀ f : IntertwiningMap (directSum (GradedMixedCompleteness.allResidual a b c d allowed))
      (trivial ℂ H ℂ), f = 0 :=
  (GradedMixedCompleteness.all_forbidden_iff a b c d allowed stable).mpr
    (all_forbidden a b c d allowed stable detect)

end Mixed
end
end Math.MixedScalarSelection
