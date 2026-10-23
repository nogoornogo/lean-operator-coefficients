import Math.RepresentationTheory.Coefficients.SpeciesCoefficientTransport
import Math.RepresentationTheory.Content.MixedSpeciesProjection
import Math.RepresentationTheory.Tensors.MixedTensorSeparation

/-! Species-preserving equivariant field changes on supported mixed coefficients. -/
namespace Math.MixedSpeciesTransport
set_option autoImplicit false
noncomputable section
open Representation
variable {P Q H : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] [Group H]
  {V V' : P → Type*} {W W' : Q → Type*}
  [∀ u, AddCommGroup (V u)] [∀ u, Module ℂ (V u)]
  [∀ u, AddCommGroup (V' u)] [∀ u, Module ℂ (V' u)]
  [∀ u, AddCommGroup (W u)] [∀ u, Module ℂ (W u)]
  [∀ u, AddCommGroup (W' u)] [∀ u, Module ℂ (W' u)]
  (r : ∀ u, Representation ℂ H (V u)) (t : ∀ u, Representation ℂ H (W u))
  (r' : ∀ u, Representation ℂ H (V' u)) (t' : ∀ u, Representation ℂ H (W' u))
  (e : ∀ u, Representation.Equiv (r u) (r' u))
  (f : ∀ u, Representation.Equiv (t u) (t' u))
  (n m : ℕ)

def domainEquiv : Representation.Equiv
    (((FiniteSpeciesExterior.representation r).exteriorPower n).tprod
      ((FiniteSpeciesExterior.representation t).symmetricPower m))
    (((FiniteSpeciesExterior.representation r').exteriorPower n).tprod
      ((FiniteSpeciesExterior.representation t').symmetricPower m)) :=
  MixedTensorSeparation.tensorCongr
    ((SpeciesCoefficientTransport.fieldsEquiv r r' e).exteriorPower n)
    ((SpeciesCoefficientTransport.fieldsEquiv t t' f).symmetricPower m)

theorem domainEquiv_pure (p : Fin n → P) (s : Fin m → Q)
    (v : ∀ i, V (p i)) (w : ∀ j, W (s j)) :
    domainEquiv r t r' t' e f n m (MixedWeightSupport.pure
      (fun i => Pi.single (p i) (v i)) (fun j => Pi.single (s j) (w j))) =
    MixedWeightSupport.pure (fun i => Pi.single (p i) (e (p i) (v i)))
      (fun j => Pi.single (s j) (f (s j) (w j))) := by
  change TensorProduct.congr _ _ (_ ⊗ₜ[ℂ] _) = _
  rw [TensorProduct.congr_tmul]
  change ((SpeciesCoefficientTransport.fieldsEquiv r r' e).exteriorPower n)
      (exteriorPower.ιMulti ℂ n (fun i => Pi.single (p i) (v i))) ⊗ₜ[ℂ]
    ((SpeciesCoefficientTransport.fieldsEquiv t t' f).symmetricPower m)
      (SymmetricPower.tprod ℂ (fun j => Pi.single (s j) (w j))) = _
  rw [Representation.Equiv.exteriorPower_apply_ιMulti,
    Representation.Equiv.symmetricPower_apply_tprod]
  simp only [SpeciesCoefficientTransport.fieldsEquiv_single, Function.comp_def,
    MixedWeightSupport.pure]

variable (allow : (Fin n → P) → (Fin m → Q) → Prop)

def pull : MixedSpeciesProjection.supportSpace allow r' t' →ₗ[ℂ]
    MixedSpeciesProjection.supportSpace allow r t where
  toFun q := ⟨q.val.comp (domainEquiv r t r' t' e f n m).toIntertwiningMap, by
    intro p s hp v w
    change q.val (domainEquiv r t r' t' e f n m (MixedWeightSupport.pure _ _)) = 0
    rw [domainEquiv_pure]
    exact q.property p s hp _ _⟩
  map_add' _ _ := by apply Subtype.ext; ext u; rfl
  map_smul' _ _ := by apply Subtype.ext; ext u; rfl

def equiv : MixedSpeciesProjection.supportSpace allow r' t' ≃ₗ[ℂ]
    MixedSpeciesProjection.supportSpace allow r t where
  toFun := pull r t r' t' e f n m allow
  invFun := pull r' t' r t (fun u => (e u).symm) (fun u => (f u).symm) n m allow
  left_inv q := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    apply MixedSpeciesExt.ext
    intro p s v w
    change q.val (domainEquiv r t r' t' e f n m
      (domainEquiv r' t' r t (fun u => (e u).symm) (fun u => (f u).symm) n m
        (MixedWeightSupport.pure _ _))) = q.val _
    rw [domainEquiv_pure, domainEquiv_pure]
    simp only [Representation.Equiv.apply_symm_apply]
  right_inv q := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    apply MixedSpeciesExt.ext
    intro p s v w
    change q.val (domainEquiv r' t' r t (fun u => (e u).symm) (fun u => (f u).symm) n m
      (domainEquiv r t r' t' e f n m (MixedWeightSupport.pure _ _))) = q.val _
    rw [domainEquiv_pure, domainEquiv_pure]
    simp only [Representation.Equiv.symm_apply_apply]
  map_add' := (pull r t r' t' e f n m allow).map_add
  map_smul' := (pull r t r' t' e f n m allow).map_smul

def allEquiv (allowed : ∀ n m : ℕ, (Fin n → P) → (Fin m → Q) → Prop) :
    (∀ z : ℕ × ℕ, MixedSpeciesProjection.supportSpace (allowed z.1 z.2) r' t') ≃ₗ[ℂ]
    (∀ z : ℕ × ℕ, MixedSpeciesProjection.supportSpace (allowed z.1 z.2) r t) :=
  LinearEquiv.piCongrRight fun z => equiv r t r' t' e f z.1 z.2 (allowed z.1 z.2)

theorem pull_id (q : MixedSpeciesProjection.supportSpace allow r t) :
    pull r t r t (fun u => Representation.Equiv.refl (r u))
      (fun u => Representation.Equiv.refl (t u)) n m allow q = q := by
  apply Subtype.ext
  apply IntertwiningMap.ext
  apply MixedSpeciesExt.ext
  intro p s v w
  change q.val (domainEquiv r t r t _ _ n m (MixedWeightSupport.pure _ _)) = q.val _
  rw [domainEquiv_pure]
  rfl

section Composition
variable {V'' : P → Type*} {W'' : Q → Type*}
  [∀ u, AddCommGroup (V'' u)] [∀ u, Module ℂ (V'' u)]
  [∀ u, AddCommGroup (W'' u)] [∀ u, Module ℂ (W'' u)]
  (r'' : ∀ u, Representation ℂ H (V'' u)) (t'' : ∀ u, Representation ℂ H (W'' u))
  (e' : ∀ u, Representation.Equiv (r' u) (r'' u))
  (f' : ∀ u, Representation.Equiv (t' u) (t'' u))

theorem pull_comp (q : MixedSpeciesProjection.supportSpace allow r'' t'') :
    pull r t r' t' e f n m allow (pull r' t' r'' t'' e' f' n m allow q) =
    pull r t r'' t'' (fun u => (e u).trans (e' u))
      (fun u => (f u).trans (f' u)) n m allow q := by
  apply Subtype.ext
  apply IntertwiningMap.ext
  apply MixedSpeciesExt.ext
  intro p s v w
  change q.val (domainEquiv r' t' r'' t'' e' f' n m
    (domainEquiv r t r' t' e f n m (MixedWeightSupport.pure _ _))) =
    q.val (domainEquiv r t r'' t'' _ _ n m (MixedWeightSupport.pure _ _))
  rw [domainEquiv_pure, domainEquiv_pure, domainEquiv_pure]
  rfl
end Composition
end
end Math.MixedSpeciesTransport
