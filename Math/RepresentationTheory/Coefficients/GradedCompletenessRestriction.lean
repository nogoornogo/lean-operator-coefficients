import Math.RepresentationTheory.Coefficients.GradedMixedCompleteness
import Math.RepresentationTheory.Coefficients.MixedCoefficientRestriction
import Math.RepresentationTheory.Relations.LocalRelationTensorNaturality
import Math.RepresentationTheory.Relations.TypedMixedLocalHomNaturality
import Math.RepresentationTheory.Constructions.TypedMixedSeparatedNaturality

/-! Residual restriction on the independently constructed content-wise carriers. -/
namespace Math.GradedCompletenessRestriction
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {P Q G H J : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [Group G] [Group H] [Group J]
  {L M : P → Type*} {K N : Q → Type*}
  [∀ u, AddCommGroup (L u)] [∀ u, Module ℂ (L u)]
  [∀ u, AddCommGroup (M u)] [∀ u, Module ℂ (M u)]
  [∀ u, AddCommGroup (K u)] [∀ u, Module ℂ (K u)]
  [∀ u, AddCommGroup (N u)] [∀ u, Module ℂ (N u)]
  (a : ∀ u, Representation ℂ G (L u)) (b : ∀ u, Representation ℂ G (K u))
  (c : ∀ u, Representation ℂ H (M u)) (d : ∀ u, Representation ℂ H (N u))
  (j : J →* H) (n m : ℕ)


@[reducible] local instance (u : P) : AddCommGroup (L u ⊗[ℂ] M u) := inferInstance
@[reducible] local instance (u : Q) : AddCommGroup (K u ⊗[ℂ] N u) := inferInstance
@[reducible] local instance : AddCommGroup (∀ u, L u ⊗[ℂ] M u) := inferInstance
@[reducible] local instance : AddCommGroup (∀ u, K u ⊗[ℂ] N u) := inferInstance


@[reducible] local instance : AddCommGroup (MixedPowerDescent.Domain
    (A := ∀ u, L u ⊗[ℂ] M u) (B := ∀ u, K u ⊗[ℂ] N u) n m) := inferInstance

@[reducible] local instance (p : Fin n → P) (s : Fin m → Q) :
    AddCommGroup (TypedMixedSeparatedHom.LocalCarrier (L := L) (K := K) p s) := inferInstance
@[reducible] local instance (p : Fin n → P) (s : Fin m → Q) :
    AddCommGroup (TypedMixedSeparatedHom.MultiplicityCarrier (M := M) (N := N) p s) := inferInstance
@[reducible] local instance (p : Fin n → P) (s : Fin m → Q) :
    AddCommGroup (TypedMixedSeparatedHom.Carrier a b c d p s) := inferInstance


omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem fieldF_comp (u : P) (gh : G × J) :
    TypedMixedSeparatedHom.fieldF a (fun u => (c u).comp j) u gh =
      TypedMixedSeparatedHom.fieldF a c u (gh.1,j gh.2) := by
  rcases gh with ⟨g,h⟩
  apply TensorProduct.ext'
  intro v w
  simp only [TypedMixedSeparatedHom.fieldF, TypedMixedLocalHom.fermion,
    CommutingActionHom.action_apply, TypedMixedSeparatedHom.localF,
    TypedMixedSeparatedHom.residualF, Representation.tprod_apply,
    TensorProduct.map_tmul, Representation.trivial_apply, MonoidHom.comp_apply]

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem fieldB_comp (u : Q) (gh : G × J) :
    TypedMixedSeparatedHom.fieldB b (fun u => (d u).comp j) u gh =
      TypedMixedSeparatedHom.fieldB b d u (gh.1,j gh.2) := by
  rcases gh with ⟨g,h⟩
  apply TensorProduct.ext'
  intro v w
  simp only [TypedMixedSeparatedHom.fieldB, TypedMixedLocalHom.boson,
    CommutingActionHom.action_apply, TypedMixedSeparatedHom.localB,
    TypedMixedSeparatedHom.residualB, Representation.tprod_apply,
    TensorProduct.map_tmul, Representation.trivial_apply, MonoidHom.comp_apply]

def inputMap : GradedMixedCompleteness.Input a b c d n m →ₗ[ℂ]
    GradedMixedCompleteness.Input a b (fun u => (c u).comp j) (fun u => (d u).comp j) n m where
  toFun f := {
    toLinearMap := f.toLinearMap
    isIntertwining' gh := by
      apply MixedPowerDescent.ext (A := ∀ u, L u ⊗[ℂ] M u)
        (B := ∀ u, K u ⊗[ℂ] N u) (N := ℂ) n m
      intro v w
      have heF : FiniteSpeciesExterior.representation
          (TypedMixedSeparatedHom.fieldF a (fun u => (c u).comp j)) gh =
          FiniteSpeciesExterior.representation (TypedMixedSeparatedHom.fieldF a c) (gh.1,j gh.2) := by
        apply LinearMap.ext
        intro x
        funext u
        exact LinearMap.congr_fun (fieldF_comp a c j u gh) (x u)
      have heB : FiniteSpeciesExterior.representation
          (TypedMixedSeparatedHom.fieldB b (fun u => (d u).comp j)) gh =
          FiniteSpeciesExterior.representation (TypedMixedSeparatedHom.fieldB b d) (gh.1,j gh.2) := by
        apply LinearMap.ext
        intro x
        funext u
        exact LinearMap.congr_fun (fieldB_comp b d j u gh) (x u)
      have h := IntertwiningMap.isIntertwining _ _ f (gh.1,j gh.2) (MixedWeightSupport.pure v w)
      simpa only [LinearMap.comp_apply, Representation.trivial_apply,
        MixedWeightSupport.pure, Representation.tprod_apply, TensorProduct.map_tmul,
        Representation.exteriorPower_apply_ιMulti, Representation.symmetricPower_apply_tprod,
        heF, heB, IntertwiningMap.toLinearMap_apply]
        using h }
  map_add' _ _ := IntertwiningMap.ext rfl
  map_smul' _ _ := IntertwiningMap.ext rfl

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem ordered_comp (p : Fin n → P) (s : Fin m → Q) (h : J) :
    TypedMixedSeparatedHom.multiplicityOrdered (fun u => (c u).comp j)
      (fun u => (d u).comp j) p s h =
    TypedMixedSeparatedHom.multiplicityOrdered c d p s (j h) := by
  apply TypedMixedTensorHom.pure_ext
  intro v w
  simp only [TypedMixedSeparatedHom.multiplicityOrdered, TypedMixedExchangeQuotient.action,
    Representation.tprod_apply, TensorProduct.map_tmul,
    MultilinearInvariantHom.tensorRepresentation_tprod, MonoidHom.comp_apply]

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem base_comp (p : Fin n → P) (s : Fin m → Q) (h : J) :
    LocalRelationTensorHom.base (TypedMixedSeparatedHom.localOrdered a b p s)
      (TypedMixedSeparatedHom.multiplicityOrdered (fun u => (c u).comp j)
        (fun u => (d u).comp j) p s) h =
    LocalRelationTensorHom.base (TypedMixedSeparatedHom.localOrdered a b p s)
      (TypedMixedSeparatedHom.multiplicityOrdered c d p s) (j h) := by
  apply TensorProduct.ext'
  intro v w
  simp only [LocalRelationTensorHom.base, Representation.tprod_apply,
    TensorProduct.map_tmul, Representation.trivial_apply,
    ordered_comp c d j n m]

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem residual_comp (p : Fin n → P) (s : Fin m → Q) (h : J) :
    TypedMixedSeparatedHom.residual a b (fun u => (c u).comp j)
      (fun u => (d u).comp j) p s h =
    TypedMixedSeparatedHom.residual a b c d p s (j h) := by
  apply LinearMap.ext
  intro q
  obtain ⟨q,rfl⟩ := (LocalRelationTensorHom.relations
    (TypedMixedSeparatedHom.localOrdered a b p s)
    (TypedMixedSeparatedHom.multiplicityOrdered c d p s)
    (TypedMixedSeparatedHom.exchangeRelations c d p s)).mkQ_surjective q
  change Submodule.Quotient.mk (LocalRelationTensorHom.base
    (TypedMixedSeparatedHom.localOrdered a b p s)
    (TypedMixedSeparatedHom.multiplicityOrdered (fun u => (c u).comp j)
      (fun u => (d u).comp j) p s) h q) =
    Submodule.Quotient.mk (LocalRelationTensorHom.base
      (TypedMixedSeparatedHom.localOrdered a b p s)
      (TypedMixedSeparatedHom.multiplicityOrdered c d p s) (j h) q)
  rw [base_comp a b c d j n m]

def factorMap (x : GradedMixedCompleteness.Content (P := P) (Q := Q) n m) :
    GradedMixedCompleteness.Factor a b c d n m x →ₗ[ℂ]
    GradedMixedCompleteness.Factor a b (fun u => (c u).comp j) (fun u => (d u).comp j) n m x where
  toFun f := {
    toLinearMap := f.toLinearMap
    isIntertwining' h := by
      apply LinearMap.ext
      intro q
      obtain ⟨q,rfl⟩ := (LocalRelationTensorHom.relations
        (TypedMixedSeparatedHom.localOrdered a b x.out.1 x.out.2)
        (TypedMixedSeparatedHom.multiplicityOrdered c d x.out.1 x.out.2)
        (TypedMixedSeparatedHom.exchangeRelations c d x.out.1 x.out.2)).mkQ_surjective q
      have he := IntertwiningMap.isIntertwining _ _ f (j h) (Submodule.Quotient.mk q)
      change f (Submodule.Quotient.mk
        (LocalRelationTensorHom.base (TypedMixedSeparatedHom.localOrdered a b x.out.1 x.out.2)
          (TypedMixedSeparatedHom.multiplicityOrdered (fun u => (c u).comp j)
            (fun u => (d u).comp j) x.out.1 x.out.2) h q)) = f (Submodule.Quotient.mk q)
      rw [base_comp a b c d j n m]
      exact he }
  map_add' _ _ := IntertwiningMap.ext rfl
  map_smul' _ _ := IntertwiningMap.ext rfl

def productMap : (∀ x, GradedMixedCompleteness.Factor a b c d n m x) →ₗ[ℂ]
    (∀ x, GradedMixedCompleteness.Factor a b
      (fun u => (c u).comp j) (fun u => (d u).comp j) n m x) :=
  LinearMap.pi fun x => (factorMap a b c d j n m x).comp (LinearMap.proj x)

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem factor_injective (x : GradedMixedCompleteness.Content (P := P) (Q := Q) n m) :
    Function.Injective (factorMap a b c d j n m x) := by
  intro f g he
  apply IntertwiningMap.ext
  exact congrArg (fun q : GradedMixedCompleteness.Factor a b
    (fun u => (c u).comp j) (fun u => (d u).comp j) n m x => q.toLinearMap) he

def factorSurjectiveEquiv (hj : Function.Surjective j)
    (x : GradedMixedCompleteness.Content (P := P) (Q := Q) n m) :
    GradedMixedCompleteness.Factor a b c d n m x ≃ₗ[ℂ]
    GradedMixedCompleteness.Factor a b (fun u => (c u).comp j)
      (fun u => (d u).comp j) n m x where
  toFun := factorMap a b c d j n m x
  invFun f := {
    toLinearMap := f.toLinearMap
    isIntertwining' h := by
      obtain ⟨h,rfl⟩ := hj h
      apply LinearMap.ext
      intro q
      change f (TypedMixedSeparatedHom.residual a b c d x.out.1 x.out.2 (j h) q) = f q
      rw [← residual_comp a b c d j n m]
      exact IntertwiningMap.isIntertwining _ _ f h q }
  left_inv _ := by apply IntertwiningMap.ext; rfl
  right_inv _ := by apply IntertwiningMap.ext; rfl
  map_add' := (factorMap a b c d j n m x).map_add
  map_smul' := (factorMap a b c d j n m x).map_smul

def productSurjectiveEquiv (hj : Function.Surjective j) :
    (∀ x, GradedMixedCompleteness.Factor a b c d n m x) ≃ₗ[ℂ]
    (∀ x, GradedMixedCompleteness.Factor a b (fun u => (c u).comp j)
      (fun u => (d u).comp j) n m x) :=
  LinearEquiv.piCongrRight fun x => factorSurjectiveEquiv a b c d j n m hj x

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem factor_id (x : GradedMixedCompleteness.Content (P := P) (Q := Q) n m)
    (q : GradedMixedCompleteness.Factor a b c d n m x) :
    factorMap a b c d (MonoidHom.id H) n m x q = q := by
  apply IntertwiningMap.ext
  rfl

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem factor_comp {T : Type*} [Group T] (k : T →* J)
    (x : GradedMixedCompleteness.Content (P := P) (Q := Q) n m)
    (q : GradedMixedCompleteness.Factor a b c d n m x) :
    factorMap a b (fun u => (c u).comp j) (fun u => (d u).comp j) k n m x
      (factorMap a b c d j n m x q) = factorMap a b c d (j.comp k) n m x q := by
  apply IntertwiningMap.ext
  rfl

omit [Fintype P] [Fintype Q] in
theorem ordered_extraction (p : Fin n → P) (s : Fin m → Q)
    (q : MixedPatternAssembly.orderedSpace (TypedMixedSeparatedHom.fieldF a c)
      (TypedMixedSeparatedHom.fieldB b d) p s)
    (q' : MixedPatternAssembly.orderedSpace
      (TypedMixedSeparatedHom.fieldF a (fun u => (c u).comp j))
      (TypedMixedSeparatedHom.fieldB b (fun u => (d u).comp j)) p s)
    (he : q'.val = q.val) :
    (TypedMixedSeparatedHom.equiv a b (fun u => (c u).comp j)
      (fun u => (d u).comp j) p s q').toLinearMap =
    (TypedMixedSeparatedHom.equiv a b c d p s q).toLinearMap := by
  apply LinearMap.ext
  intro u
  obtain ⟨u,rfl⟩ := (LocalRelationTensorHom.relations
    (TypedMixedSeparatedHom.localOrdered a b p s)
    (TypedMixedSeparatedHom.multiplicityOrdered c d p s)
    (TypedMixedSeparatedHom.exchangeRelations c d p s)).mkQ_surjective u
  have hgen :
      (TypedMixedSeparatedHom.equiv a b (fun u => (c u).comp j)
        (fun u => (d u).comp j) p s q').toLinearMap.comp
        (LocalRelationTensorHom.relations
          (TypedMixedSeparatedHom.localOrdered a b p s)
          (TypedMixedSeparatedHom.multiplicityOrdered (fun u => (c u).comp j)
            (fun u => (d u).comp j) p s)
          (TypedMixedSeparatedHom.exchangeRelations (fun u => (c u).comp j)
            (fun u => (d u).comp j) p s)).mkQ =
      (TypedMixedSeparatedHom.equiv a b c d p s q).toLinearMap.comp
        (LocalRelationTensorHom.relations
          (TypedMixedSeparatedHom.localOrdered a b p s)
          (TypedMixedSeparatedHom.multiplicityOrdered c d p s)
          (TypedMixedSeparatedHom.exchangeRelations c d p s)).mkQ := by
    apply TensorProduct.ext'
    intro l v
    obtain ⟨l,rfl⟩ := (LocalCoinvariantHom.relations
      (TypedMixedSeparatedHom.localOrdered a b p s)).mkQ_surjective l
    simp only [LinearMap.comp_apply, IntertwiningMap.toLinearMap_apply]
    rw [TypedMixedSeparatedHom.equiv_generator, TypedMixedSeparatedHom.equiv_generator, he]
  exact LinearMap.congr_fun hgen u

theorem extraction (f : GradedMixedCompleteness.Input a b c d n m) :
    GradedMixedCompleteness.equiv a b (fun u => (c u).comp j) (fun u => (d u).comp j) n m
      (inputMap a b c d j n m f) =
    productMap a b c d j n m (GradedMixedCompleteness.equiv a b c d n m f) := by
  funext x
  apply IntertwiningMap.ext
  apply ordered_extraction a b c d j n m x.out.1 x.out.2
  rfl

theorem reconstruction (q : ∀ x, GradedMixedCompleteness.Factor a b c d n m x) :
    (GradedMixedCompleteness.equiv a b (fun u => (c u).comp j) (fun u => (d u).comp j) n m).symm
      (productMap a b c d j n m q) =
    inputMap a b c d j n m ((GradedMixedCompleteness.equiv a b c d n m).symm q) := by
  apply (GradedMixedCompleteness.equiv a b (fun u => (c u).comp j)
    (fun u => (d u).comp j) n m).injective
  rw [LinearEquiv.apply_symm_apply, extraction, LinearEquiv.apply_symm_apply]

section Selection
variable (allow : (Fin n → P) → (Fin m → Q) → Prop)
  [∀ p s, Decidable (allow p s)]
  (stable : ∀ p s (e : Equiv.Perm (Fin n)) (f : Equiv.Perm (Fin m)),
    allow (p ∘ e) (s ∘ f) ↔ allow p s)

def selectedMap : MixedSpeciesProjection.supportSpace allow
    (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d) →ₗ[ℂ]
    MixedSpeciesProjection.supportSpace allow
      (TypedMixedSeparatedHom.fieldF a (fun u => (c u).comp j))
      (TypedMixedSeparatedHom.fieldB b (fun u => (d u).comp j)) where
  toFun f := ⟨inputMap a b c d j n m f.val, f.property⟩
  map_add' _ _ := Subtype.ext (IntertwiningMap.ext rfl)
  map_smul' _ _ := Subtype.ext (IntertwiningMap.ext rfl)

def selectedProductMap :
    (∀ x : MixedContentOrbits.Selected allow, GradedMixedCompleteness.Factor a b c d n m x.val) →ₗ[ℂ]
    (∀ x : MixedContentOrbits.Selected allow, GradedMixedCompleteness.Factor a b
      (fun u => (c u).comp j) (fun u => (d u).comp j) n m x.val) :=
  LinearMap.pi fun x => (factorMap a b c d j n m x.val).comp (LinearMap.proj x)

theorem selected_extraction (f : MixedSpeciesProjection.supportSpace allow
    (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d)) :
    GradedMixedCompleteness.selectedEquiv a b (fun u => (c u).comp j)
      (fun u => (d u).comp j) n m allow stable (selectedMap a b c d j n m allow f) =
    selectedProductMap a b c d j n m allow
      (GradedMixedCompleteness.selectedEquiv a b c d n m allow stable f) := by
  funext x
  apply IntertwiningMap.ext
  apply ordered_extraction a b c d j n m x.val.out.1 x.val.out.2
  rfl
end Selection
end
end Math.GradedCompletenessRestriction
