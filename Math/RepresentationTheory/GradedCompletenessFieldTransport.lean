import Math.RepresentationTheory.TypedMixedSeparatedTransport
import Math.RepresentationTheory.MixedSpeciesTransport
import Math.RepresentationTheory.MixedContentEvaluation
import Math.RepresentationTheory.GradedMixedCompleteness

/-! Arbitrary-degree field presentation naturality, with directly induced
coinvariant/exchange carrier equivalences for each field content. -/
namespace Math.GradedCompletenessFieldTransport
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {P Q G H : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [Group G] [Group H]
  {L M L' M' : P → Type*} {K N K' N' : Q → Type*}
  [∀ u, AddCommGroup (L u)] [∀ u, Module ℂ (L u)]
  [∀ u, AddCommGroup (M u)] [∀ u, Module ℂ (M u)]
  [∀ u, AddCommGroup (K u)] [∀ u, Module ℂ (K u)]
  [∀ u, AddCommGroup (N u)] [∀ u, Module ℂ (N u)]
  [∀ u, AddCommGroup (L' u)] [∀ u, Module ℂ (L' u)]
  [∀ u, AddCommGroup (M' u)] [∀ u, Module ℂ (M' u)]
  [∀ u, AddCommGroup (K' u)] [∀ u, Module ℂ (K' u)]
  [∀ u, AddCommGroup (N' u)] [∀ u, Module ℂ (N' u)]
  (a : ∀ u, Representation ℂ G (L u)) (b : ∀ u, Representation ℂ G (K u))
  (c : ∀ u, Representation ℂ H (M u)) (d : ∀ u, Representation ℂ H (N u))
  (a' : ∀ u, Representation ℂ G (L' u)) (b' : ∀ u, Representation ℂ G (K' u))
  (c' : ∀ u, Representation ℂ H (M' u)) (d' : ∀ u, Representation ℂ H (N' u))
  (e : ∀ u, Representation.Equiv (TypedMixedSeparatedHom.residualF (L := L) c u)
    (TypedMixedSeparatedHom.residualF (L := L') c' u))
  (f : ∀ u, Representation.Equiv (TypedMixedSeparatedHom.residualB (K := K) d u)
    (TypedMixedSeparatedHom.residualB (K := K') d' u))
  (he : ∀ u g v, e u (TypedMixedSeparatedHom.localF (M := M) a u g v) =
    TypedMixedSeparatedHom.localF (M := M') a' u g (e u v))
  (hf : ∀ u g w, f u (TypedMixedSeparatedHom.localB (N := N) b u g w) =
    TypedMixedSeparatedHom.localB (N := N') b' u g (f u w))
  (n m : ℕ)

@[reducible] local instance (u : P) : AddCommGroup (L u ⊗[ℂ] M u) := inferInstance
@[reducible] local instance (u : Q) : AddCommGroup (K u ⊗[ℂ] N u) := inferInstance
@[reducible] local instance (u : P) : AddCommGroup (L' u ⊗[ℂ] M' u) := inferInstance
@[reducible] local instance (u : Q) : AddCommGroup (K' u ⊗[ℂ] N' u) := inferInstance
@[reducible] local instance : AddCommGroup (∀ u, L u ⊗[ℂ] M u) := inferInstance
@[reducible] local instance : AddCommGroup (∀ u, K u ⊗[ℂ] N u) := inferInstance
@[reducible] local instance : AddCommGroup (∀ u, L' u ⊗[ℂ] M' u) := inferInstance
@[reducible] local instance : AddCommGroup (∀ u, K' u ⊗[ℂ] N' u) := inferInstance
@[reducible] local instance : AddCommGroup (MixedPowerDescent.Domain
    (A := ∀ u, L u ⊗[ℂ] M u) (B := ∀ u, K u ⊗[ℂ] N u) n m) := inferInstance
@[reducible] local instance : AddCommGroup (MixedPowerDescent.Domain
    (A := ∀ u, L' u ⊗[ℂ] M' u) (B := ∀ u, K' u ⊗[ℂ] N' u) n m) := inferInstance

include he in
def fermionEquiv (u : P) : Representation.Equiv
    (TypedMixedSeparatedHom.fieldF a c u) (TypedMixedSeparatedHom.fieldF a' c' u) where
  toLinearEquiv := (e u).toLinearEquiv
  isIntertwining' gh := by
    apply LinearMap.ext
    intro v
    change e u (TypedMixedSeparatedHom.localF (M := M) a u gh.1
      (TypedMixedSeparatedHom.residualF (L := L) c u gh.2 v)) =
      TypedMixedSeparatedHom.localF (M := M') a' u gh.1
        (TypedMixedSeparatedHom.residualF (L := L') c' u gh.2 (e u v))
    rw [he]
    exact congrArg (TypedMixedSeparatedHom.localF (M := M') a' u gh.1)
      (IntertwiningMap.isIntertwining _ _ (e u).toIntertwiningMap gh.2 v)

include hf in
def bosonEquiv (u : Q) : Representation.Equiv
    (TypedMixedSeparatedHom.fieldB b d u) (TypedMixedSeparatedHom.fieldB b' d' u) where
  toLinearEquiv := (f u).toLinearEquiv
  isIntertwining' gh := by
    apply LinearMap.ext
    intro w
    change f u (TypedMixedSeparatedHom.localB (N := N) b u gh.1
      (TypedMixedSeparatedHom.residualB (K := K) d u gh.2 w)) =
      TypedMixedSeparatedHom.localB (N := N') b' u gh.1
        (TypedMixedSeparatedHom.residualB (K := K') d' u gh.2 (f u w))
    rw [hf]
    exact congrArg (TypedMixedSeparatedHom.localB (N := N') b' u gh.1)
      (IntertwiningMap.isIntertwining _ _ (f u).toIntertwiningMap gh.2 w)

abbrev fieldMap := MixedSpeciesTransport.domainEquiv
  (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d)
  (TypedMixedSeparatedHom.fieldF a' c') (TypedMixedSeparatedHom.fieldB b' d')
  (fermionEquiv a c a' c' e he) (bosonEquiv b d b' d' f hf) n m

def inputMap : GradedMixedCompleteness.Input a' b' c' d' n m →ₗ[ℂ]
    GradedMixedCompleteness.Input a b c d n m where
  toFun q := q.comp (fieldMap a b c d a' b' c' d' e f he hf n m).toIntertwiningMap
  map_add' _ _ := by ext u; rfl
  map_smul' _ _ := by ext u; rfl

def productEquiv : (∀ x, GradedMixedCompleteness.Factor a' b' c' d' n m x) ≃ₗ[ℂ]
    (∀ x, GradedMixedCompleteness.Factor a b c d n m x) :=
  LinearEquiv.piCongrRight fun x => TypedMixedSeparatedTransport.homEquiv
    a b c d a' b' c' d' e f he hf x.out.1 x.out.2

theorem ordered_extraction (q : GradedMixedCompleteness.Input a' b' c' d' n m)
    (x : GradedMixedCompleteness.Content (P := P) (Q := Q) n m) :
    MixedContentOrbits.equiv (TypedMixedSeparatedHom.fieldF a c)
      (TypedMixedSeparatedHom.fieldB b d) (inputMap a b c d a' b' c' d' e f he hf n m q) x =
    TypedMixedSeparatedTransport.inputPull a b c d a' b' c' d' e f he hf x.out.1 x.out.2
      (MixedContentOrbits.equiv (TypedMixedSeparatedHom.fieldF a' c')
        (TypedMixedSeparatedHom.fieldB b' d') q x) := by
  apply Subtype.ext
  ext v w
  rw [TypedMixedSeparatedTransport.inputPull_apply, MixedContentOrbits.equiv_apply,
    MixedContentOrbits.equiv_apply]
  change q (fieldMap a b c d a' b' c' d' e f he hf n m (MixedWeightSupport.pure _ _)) = _
  rw [MixedSpeciesTransport.domainEquiv_pure]
  rfl

theorem extraction (q : GradedMixedCompleteness.Input a' b' c' d' n m) :
    GradedMixedCompleteness.equiv a b c d n m (inputMap a b c d a' b' c' d' e f he hf n m q) =
    productEquiv a b c d a' b' c' d' e f he hf n m
      (GradedMixedCompleteness.equiv a' b' c' d' n m q) := by
  funext x
  change TypedMixedSeparatedHom.equiv a b c d x.out.1 x.out.2
    (MixedContentOrbits.equiv _ _ _ x) = _
  rw [ordered_extraction]
  exact TypedMixedSeparatedTransport.extraction a b c d a' b' c' d' e f he hf x.out.1 x.out.2 _

theorem reconstruction (q : ∀ x, GradedMixedCompleteness.Factor a' b' c' d' n m x) :
    (GradedMixedCompleteness.equiv a b c d n m).symm
      (productEquiv a b c d a' b' c' d' e f he hf n m q) =
    inputMap a b c d a' b' c' d' e f he hf n m
      ((GradedMixedCompleteness.equiv a' b' c' d' n m).symm q) := by
  have h := extraction a b c d a' b' c' d' e f he hf n m
    ((GradedMixedCompleteness.equiv a' b' c' d' n m).symm q)
  rw [LinearEquiv.apply_symm_apply] at h
  exact (LinearEquiv.symm_apply_eq _).mpr h.symm

section Selection
variable (allow : (Fin n → P) → (Fin m → Q) → Prop)
  [∀ p s, Decidable (allow p s)]
  (stable : ∀ p s (u : Equiv.Perm (Fin n)) (v : Equiv.Perm (Fin m)),
    allow (p ∘ u) (s ∘ v) ↔ allow p s)

def selectedInputEquiv : MixedSpeciesProjection.supportSpace allow
    (TypedMixedSeparatedHom.fieldF a' c') (TypedMixedSeparatedHom.fieldB b' d') ≃ₗ[ℂ]
    MixedSpeciesProjection.supportSpace allow
      (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d) :=
  MixedSpeciesTransport.equiv _ _ _ _ (fermionEquiv a c a' c' e he)
    (bosonEquiv b d b' d' f hf) n m allow

def selectedProductEquiv :
    (∀ x : MixedContentOrbits.Selected allow, GradedMixedCompleteness.Factor a' b' c' d' n m x.val) ≃ₗ[ℂ]
    (∀ x : MixedContentOrbits.Selected allow, GradedMixedCompleteness.Factor a b c d n m x.val) :=
  LinearEquiv.piCongrRight fun x => TypedMixedSeparatedTransport.homEquiv
    a b c d a' b' c' d' e f he hf x.val.out.1 x.val.out.2

theorem selected_extraction (q : MixedSpeciesProjection.supportSpace allow
    (TypedMixedSeparatedHom.fieldF a' c') (TypedMixedSeparatedHom.fieldB b' d')) :
    GradedMixedCompleteness.selectedEquiv a b c d n m allow stable
      (selectedInputEquiv a b c d a' b' c' d' e f he hf n m allow q) =
    selectedProductEquiv a b c d a' b' c' d' e f he hf n m allow
      (GradedMixedCompleteness.selectedEquiv a' b' c' d' n m allow stable q) := by
  funext x
  have ho : MixedContentOrbits.selectedEquiv (TypedMixedSeparatedHom.fieldF a c)
      (TypedMixedSeparatedHom.fieldB b d) allow stable
      (selectedInputEquiv a b c d a' b' c' d' e f he hf n m allow q) x =
      TypedMixedSeparatedTransport.inputPull a b c d a' b' c' d' e f he hf x.val.out.1 x.val.out.2
        (MixedContentOrbits.selectedEquiv (TypedMixedSeparatedHom.fieldF a' c')
          (TypedMixedSeparatedHom.fieldB b' d') allow stable q x) := by
    apply Subtype.ext
    ext v w
    rw [TypedMixedSeparatedTransport.inputPull_apply, MixedContentOrbits.selectedEquiv_apply,
      MixedContentOrbits.selectedEquiv_apply]
    change q.val (fieldMap a b c d a' b' c' d' e f he hf n m (MixedWeightSupport.pure _ _)) = _
    rw [MixedSpeciesTransport.domainEquiv_pure]
    rfl
  change TypedMixedSeparatedHom.equiv a b c d x.val.out.1 x.val.out.2
    (MixedContentOrbits.selectedEquiv _ _ _ _ _ x) = _
  rw [ho]
  exact TypedMixedSeparatedTransport.extraction a b c d a' b' c' d' e f he hf x.val.out.1 x.val.out.2 _

theorem selected_reconstruction (q : ∀ x : MixedContentOrbits.Selected allow,
    GradedMixedCompleteness.Factor a' b' c' d' n m x.val) :
    (GradedMixedCompleteness.selectedEquiv a b c d n m allow stable).symm
      (selectedProductEquiv a b c d a' b' c' d' e f he hf n m allow q) =
    selectedInputEquiv a b c d a' b' c' d' e f he hf n m allow
      ((GradedMixedCompleteness.selectedEquiv a' b' c' d' n m allow stable).symm q) := by
  have h := selected_extraction a b c d a' b' c' d' e f he hf n m allow stable
    ((GradedMixedCompleteness.selectedEquiv a' b' c' d' n m allow stable).symm q)
  rw [LinearEquiv.apply_symm_apply] at h
  exact (LinearEquiv.symm_apply_eq _).mpr h.symm
end Selection

section AllDegrees
variable (allowed : ∀ n m : ℕ, (Fin n → P) → (Fin m → Q) → Prop)
  [∀ n m p s, Decidable (allowed n m p s)]
  (stableAll : ∀ n m p s (u : Equiv.Perm (Fin n)) (v : Equiv.Perm (Fin m)),
    allowed n m (p ∘ u) (s ∘ v) ↔ allowed n m p s)

def allInputEquiv :
    (∀ z : ℕ × ℕ, MixedSpeciesProjection.supportSpace (allowed z.1 z.2)
      (TypedMixedSeparatedHom.fieldF a' c') (TypedMixedSeparatedHom.fieldB b' d')) ≃ₗ[ℂ]
    (∀ z : ℕ × ℕ, MixedSpeciesProjection.supportSpace (allowed z.1 z.2)
      (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d)) :=
  LinearEquiv.piCongrRight fun z =>
    selectedInputEquiv a b c d a' b' c' d' e f he hf z.1 z.2 (allowed z.1 z.2)

def allFactorEquiv :
    (∀ x : GradedMixedCompleteness.AllIndex allowed,
      GradedMixedCompleteness.Factor a' b' c' d' x.1.1 x.1.2 x.2.val) ≃ₗ[ℂ]
    (∀ x : GradedMixedCompleteness.AllIndex allowed,
      GradedMixedCompleteness.Factor a b c d x.1.1 x.1.2 x.2.val) :=
  LinearEquiv.piCongrRight fun x => TypedMixedSeparatedTransport.homEquiv
    a b c d a' b' c' d' e f he hf x.2.val.out.1 x.2.val.out.2

def dualEquiv : IntertwiningMap (directSum (GradedMixedCompleteness.allResidual a b c d allowed))
    (trivial ℂ H ℂ) ≃ₗ[ℂ]
    (∀ x : GradedMixedCompleteness.AllIndex allowed,
      GradedMixedCompleteness.Factor a b c d x.1.1 x.1.2 x.2.val) := by
  classical
  exact DirectSumFunctionalProduct.equiv (I := GradedMixedCompleteness.AllIndex allowed)
    (H := H) (V := fun x => TypedMixedSeparatedHom.Carrier a b c d x.2.val.out.1 x.2.val.out.2)
    (GradedMixedCompleteness.allResidual a b c d allowed)

/-- Assembled from independent quotient-carrier maps and the direct-sum
universal property, not from operator completeness. -/
def allHomEquiv :
    IntertwiningMap (directSum (GradedMixedCompleteness.allResidual a' b' c' d' allowed))
      (trivial ℂ H ℂ) ≃ₗ[ℂ]
    IntertwiningMap (directSum (GradedMixedCompleteness.allResidual a b c d allowed))
      (trivial ℂ H ℂ) :=
  (dualEquiv a' b' c' d' allowed).trans
    ((allFactorEquiv a b c d a' b' c' d' e f he hf allowed).trans
      (dualEquiv a b c d allowed).symm)

theorem all_extraction (q : ∀ z : ℕ × ℕ,
    MixedSpeciesProjection.supportSpace (allowed z.1 z.2)
      (TypedMixedSeparatedHom.fieldF a' c') (TypedMixedSeparatedHom.fieldB b' d')) :
    GradedMixedCompleteness.allEquiv a b c d allowed stableAll
      (allInputEquiv a b c d a' b' c' d' e f he hf allowed q) =
    allHomEquiv a b c d a' b' c' d' e f he hf allowed
      (GradedMixedCompleteness.allEquiv a' b' c' d' allowed stableAll q) := by
  classical
  apply (dualEquiv a b c d allowed).injective
  simp only [GradedMixedCompleteness.allEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, allHomEquiv, dualEquiv]
  funext x
  exact congrFun (selected_extraction a b c d a' b' c' d' e f he hf
    x.1.1 x.1.2 (allowed x.1.1 x.1.2) (stableAll x.1.1 x.1.2) (q x.1)) x.2

theorem all_reconstruction (q : IntertwiningMap
    (directSum (GradedMixedCompleteness.allResidual a' b' c' d' allowed)) (trivial ℂ H ℂ)) :
    (GradedMixedCompleteness.allEquiv a b c d allowed stableAll).symm
      (allHomEquiv a b c d a' b' c' d' e f he hf allowed q) =
    allInputEquiv a b c d a' b' c' d' e f he hf allowed
      ((GradedMixedCompleteness.allEquiv a' b' c' d' allowed stableAll).symm q) := by
  have h := all_extraction a b c d a' b' c' d' e f he hf allowed stableAll
    ((GradedMixedCompleteness.allEquiv a' b' c' d' allowed stableAll).symm q)
  have hh := congrArg (allHomEquiv a b c d a' b' c' d' e f he hf allowed)
    ((GradedMixedCompleteness.allEquiv a' b' c' d' allowed stableAll).apply_symm_apply q)
  exact (LinearEquiv.symm_apply_eq _).mpr (h.trans hh).symm
end AllDegrees
end
end Math.GradedCompletenessFieldTransport
