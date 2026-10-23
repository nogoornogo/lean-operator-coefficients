import Math.RepresentationTheory.Coefficients.GradedCompletenessRestriction

/-! All-degree restriction is assembled by the direct-sum universal property. -/
namespace Math.GradedCompletenessAllRestriction
set_option autoImplicit false
noncomputable section
open Representation
variable {P Q G H J : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [Group G] [Group H] [Group J]
  {L M : P → Type*} {K N : Q → Type*}
  [∀ u, AddCommGroup (L u)] [∀ u, Module ℂ (L u)]
  [∀ u, AddCommGroup (M u)] [∀ u, Module ℂ (M u)]
  [∀ u, AddCommGroup (K u)] [∀ u, Module ℂ (K u)]
  [∀ u, AddCommGroup (N u)] [∀ u, Module ℂ (N u)]
  (a : ∀ u, Representation ℂ G (L u)) (b : ∀ u, Representation ℂ G (K u))
  (c : ∀ u, Representation ℂ H (M u)) (d : ∀ u, Representation ℂ H (N u))
  (j : J →* H)
  (allowed : ∀ n m : ℕ, (Fin n → P) → (Fin m → Q) → Prop)
  [∀ n m v w, Decidable (allowed n m v w)]
  (stable : ∀ n m v w (p : Equiv.Perm (Fin n)) (q : Equiv.Perm (Fin m)),
    allowed n m (v ∘ p) (w ∘ q) ↔ allowed n m v w)

abbrev Input := ∀ z : ℕ × ℕ, MixedSpeciesProjection.supportSpace (allowed z.1 z.2)
  (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d)

def inputMap : Input a b c d allowed →ₗ[ℂ]
    Input a b (fun u => (c u).comp j) (fun u => (d u).comp j) allowed :=
  LinearMap.pi fun z =>
    (GradedCompletenessRestriction.selectedMap a b c d j z.1 z.2 (allowed z.1 z.2)).comp
      (LinearMap.proj z)

def factorMap :
    (∀ x : GradedMixedCompleteness.AllIndex allowed,
      GradedMixedCompleteness.Factor a b c d x.1.1 x.1.2 x.2.val) →ₗ[ℂ]
    (∀ x : GradedMixedCompleteness.AllIndex allowed,
      GradedMixedCompleteness.Factor a b (fun u => (c u).comp j)
        (fun u => (d u).comp j) x.1.1 x.1.2 x.2.val) :=
  LinearMap.pi fun x =>
    (GradedCompletenessRestriction.factorMap a b c d j x.1.1 x.1.2 x.2.val).comp
      (LinearMap.proj x)

def dualEquiv : IntertwiningMap
    (directSum (GradedMixedCompleteness.allResidual a b c d allowed)) (trivial ℂ H ℂ) ≃ₗ[ℂ]
    (∀ x : GradedMixedCompleteness.AllIndex allowed,
      GradedMixedCompleteness.Factor a b c d x.1.1 x.1.2 x.2.val) := by
  classical
  exact DirectSumFunctionalProduct.equiv (I := GradedMixedCompleteness.AllIndex allowed)
    (H := H) (V := fun x => TypedMixedSeparatedHom.Carrier a b c d x.2.val.out.1 x.2.val.out.2)
    (GradedMixedCompleteness.allResidual a b c d allowed)

/-- Only independently defined quotient-factor maps and the direct-sum dual
universal property enter this construction, not operator completeness. -/
def homMap :
    IntertwiningMap (directSum (GradedMixedCompleteness.allResidual a b c d allowed))
      (trivial ℂ H ℂ) →ₗ[ℂ]
    IntertwiningMap (directSum (GradedMixedCompleteness.allResidual a b
      (fun u => (c u).comp j) (fun u => (d u).comp j) allowed)) (trivial ℂ J ℂ) := by
  classical
  exact (dualEquiv a b (fun u => (c u).comp j)
      (fun u => (d u).comp j) allowed).symm.toLinearMap.comp
    ((factorMap a b c d j allowed).comp
      (dualEquiv a b c d allowed).toLinearMap)

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [∀ n m v w, Decidable (allowed n m v w)] in
theorem factorMap_injective : Function.Injective (factorMap a b c d j allowed) := by
  intro f g h
  funext x
  exact GradedCompletenessRestriction.factor_injective a b c d j x.1.1 x.1.2 x.2.val
    (congrFun h x)

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [∀ n m v w, Decidable (allowed n m v w)] in
theorem homMap_injective : Function.Injective (homMap a b c d j allowed) := by
  intro f g h
  apply (dualEquiv a b c d allowed).injective
  apply factorMap_injective a b c d j allowed
  exact (dualEquiv a b (fun u => (c u).comp j)
    (fun u => (d u).comp j) allowed).symm.injective h

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [∀ n m v w, Decidable (allowed n m v w)] in
theorem nonzero (f : IntertwiningMap
    (directSum (GradedMixedCompleteness.allResidual a b c d allowed)) (trivial ℂ H ℂ))
    (hf : f ≠ 0) : homMap a b c d j allowed f ≠ 0 := by
  intro h
  exact hf (homMap_injective a b c d j allowed (h.trans (map_zero _).symm))

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [∀ n m v w, Decidable (allowed n m v w)] in
theorem forbidden (h : ∀ f : IntertwiningMap
    (directSum (GradedMixedCompleteness.allResidual a b
      (fun u => (c u).comp j) (fun u => (d u).comp j) allowed)) (trivial ℂ J ℂ), f = 0) :
    ∀ f : IntertwiningMap (directSum (GradedMixedCompleteness.allResidual a b c d allowed))
      (trivial ℂ H ℂ), f = 0 := by
  intro f
  exact homMap_injective a b c d j allowed ((h _).trans (map_zero _).symm)

def factorSurjectiveEquiv (hj : Function.Surjective j) :
    (∀ x : GradedMixedCompleteness.AllIndex allowed,
      GradedMixedCompleteness.Factor a b c d x.1.1 x.1.2 x.2.val) ≃ₗ[ℂ]
    (∀ x : GradedMixedCompleteness.AllIndex allowed,
      GradedMixedCompleteness.Factor a b (fun u => (c u).comp j)
        (fun u => (d u).comp j) x.1.1 x.1.2 x.2.val) :=
  LinearEquiv.piCongrRight fun x =>
    GradedCompletenessRestriction.factorSurjectiveEquiv a b c d j x.1.1 x.1.2 hj x.2.val

def surjectiveEquiv (hj : Function.Surjective j) :
    IntertwiningMap (directSum (GradedMixedCompleteness.allResidual a b c d allowed))
      (trivial ℂ H ℂ) ≃ₗ[ℂ]
    IntertwiningMap (directSum (GradedMixedCompleteness.allResidual a b
      (fun u => (c u).comp j) (fun u => (d u).comp j) allowed)) (trivial ℂ J ℂ) :=
  (dualEquiv a b c d allowed).trans ((factorSurjectiveEquiv a b c d j allowed hj).trans
    (dualEquiv a b (fun u => (c u).comp j) (fun u => (d u).comp j) allowed).symm)

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [∀ n m v w, Decidable (allowed n m v w)] in
theorem surjectiveEquiv_apply (hj : Function.Surjective j) (f) :
    surjectiveEquiv a b c d j allowed hj f = homMap a b c d j allowed f := rfl

include stable in
theorem extraction (f : Input a b c d allowed) :
    GradedMixedCompleteness.allEquiv a b (fun u => (c u).comp j)
      (fun u => (d u).comp j) allowed stable (inputMap a b c d j allowed f) =
    homMap a b c d j allowed (GradedMixedCompleteness.allEquiv a b c d allowed stable f) := by
  classical
  apply (dualEquiv a b (fun u => (c u).comp j)
      (fun u => (d u).comp j) allowed).injective
  simp only [GradedMixedCompleteness.allEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, homMap, dualEquiv, LinearMap.comp_apply, LinearEquiv.coe_coe]
  funext x
  exact congrFun (GradedCompletenessRestriction.selected_extraction a b c d j
    x.1.1 x.1.2 (allowed x.1.1 x.1.2) (stable x.1.1 x.1.2) (f x.1)) x.2

include stable in
theorem reconstruction (q : IntertwiningMap
    (directSum (GradedMixedCompleteness.allResidual a b c d allowed)) (trivial ℂ H ℂ)) :
    (GradedMixedCompleteness.allEquiv a b (fun u => (c u).comp j)
      (fun u => (d u).comp j) allowed stable).symm (homMap a b c d j allowed q) =
    inputMap a b c d j allowed ((GradedMixedCompleteness.allEquiv a b c d allowed stable).symm q) := by
  have h := extraction a b c d j allowed stable
    ((GradedMixedCompleteness.allEquiv a b c d allowed stable).symm q)
  have hh := congrArg (homMap a b c d j allowed)
    ((GradedMixedCompleteness.allEquiv a b c d allowed stable).apply_symm_apply q)
  have he := h.trans hh
  exact ((GradedMixedCompleteness.allEquiv a b (fun u => (c u).comp j)
    (fun u => (d u).comp j) allowed stable).symm_apply_eq).mpr he.symm
end
end Math.GradedCompletenessAllRestriction
