import Math.RepresentationTheory.Decomposition.ProductIrreducibility
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.Tactic

/-!
# Factorization of irreducible product representations

This file develops the converse to irreducibility of an external tensor
product.  Given a `G`-irreducible `rho` occurring in the restriction of a
`G x H` representation `tau`, the multiplicity space

`Hom_G(rho, tau|G)`

carries an `H`-representation by postcomposition.  Evaluation is then a
`G x H` intertwiner from the corresponding external tensor product to `tau`.
-/

namespace Math
namespace ProductFactorization

open TensorProduct ExternalTensorProduct ProductIrreducibility Burnside
open scoped MonoidAlgebra

noncomputable section

variable {k G H U T : Type*}
variable [Field k] [Group G] [Group H]
variable [AddCommGroup U] [Module k U]
variable [AddCommGroup T] [Module k T]

/-- Restriction of a product representation to its first factor. -/
def firstRestriction (tau : Representation k (G × H) T) :
    Representation k G T :=
  tau.comp (MonoidHom.inl G H)

/-- Restriction of a product representation to its second factor. -/
def secondRestriction (tau : Representation k (G × H) T) :
    Representation k H T :=
  tau.comp (MonoidHom.inr G H)

@[simp]
theorem firstRestriction_apply
    (tau : Representation k (G × H) T) (g : G) :
    firstRestriction tau g = tau (g, 1) :=
  rfl

@[simp]
theorem secondRestriction_apply
    (tau : Representation k (G × H) T) (h : H) :
    secondRestriction tau h = tau (1, h) :=
  rfl

variable (tau : Representation k (G × H) T)
variable (rho : Representation k G U)

abbrev MultiplicitySpace :=
  Representation.IntertwiningMap rho (firstRestriction tau)

/-- The second factor acts on the multiplicity space by postcomposition. -/
def multiplicityAction (h : H) :
    MultiplicitySpace tau rho →ₗ[k] MultiplicitySpace tau rho where
  toFun f :=
    { toLinearMap := (tau (1, h)).comp f.toLinearMap
      isIntertwining' g := by
        apply LinearMap.ext
        intro u
        simp only [LinearMap.comp_apply]
        change tau (1, h) (f (rho g u)) =
          tau (g, 1) (tau (1, h) (f u))
        rw [f.isIntertwining]
        change tau (1, h) (tau (g, 1) (f u)) =
          tau (g, 1) (tau (1, h) (f u))
        calc
          _ = tau ((1, h) * (g, 1)) (f u) := by
            rw [map_mul, Module.End.mul_apply]
          _ = tau ((g, 1) * (1, h)) (f u) := by simp
          _ = _ := by rw [map_mul, Module.End.mul_apply] }
  map_add' f f' := by
    ext u
    simp
  map_smul' a f := by
    ext u
    simp

@[simp]
theorem multiplicityAction_apply
    (h : H) (f : MultiplicitySpace tau rho) (u : U) :
    multiplicityAction tau rho h f u = tau (1, h) (f u) :=
  rfl

/-- The canonical `H`-representation on `Hom_G(rho, tau|G)`. -/
def multiplicityRepresentation :
    Representation k H (MultiplicitySpace tau rho) where
  toFun := multiplicityAction tau rho
  map_one' := by
    apply LinearMap.ext
    intro f
    ext u
    change tau (1 : G × H) (f u) = f u
    rw [map_one]
    rfl
  map_mul' h h' := by
    apply LinearMap.ext
    intro f
    ext u
    change tau (1, h * h') (f u) =
      tau (1, h) (tau (1, h') (f u))
    rw [← Module.End.mul_apply, ← map_mul]
    simp

@[simp]
theorem multiplicityRepresentation_apply
    (h : H) (f : MultiplicitySpace tau rho) (u : U) :
    multiplicityRepresentation tau rho h f u = tau (1, h) (f u) :=
  rfl

/-- Evaluation at a fixed first-factor vector intertwines the canonical
multiplicity representation with the second-factor restriction. -/
def multiplicityEvaluationAt (u : U) :
    Representation.IntertwiningMap
      (multiplicityRepresentation tau rho) (secondRestriction tau) where
  toLinearMap :=
    { toFun := fun f => f u
      map_add' := fun f f' => by simp
      map_smul' := fun a f => by simp }
  isIntertwining' h := by
    apply LinearMap.ext
    intro f
    rfl

@[simp]
theorem multiplicityEvaluationAt_apply
    (u : U) (f : MultiplicitySpace tau rho) :
    multiplicityEvaluationAt tau rho u f = f u :=
  rfl

/-- Evaluation at a nonzero vector is injective when the first-factor
representation is irreducible. -/
theorem multiplicityEvaluationAt_injective
    [Representation.IsIrreducible rho]
    {u : U} (hu : u ≠ 0) :
    Function.Injective (multiplicityEvaluationAt tau rho u) := by
  intro f f' hff'
  have hAt : (f - f') u = 0 := by
    simpa using sub_eq_zero.mpr hff'
  have hZero : f - f' = 0 := by
    rcases Representation.IsIrreducible.injective_or_eq_zero (f - f') with
      hInjective | hZero
    · exfalso
      apply hu
      apply hInjective
      simpa using hAt
    · exact hZero
  exact sub_eq_zero.mp hZero

/-- The evaluation image as an actual subrepresentation of the second-factor
restriction.  Unlike the abstract intertwiner space, this subtype inherits
the ambient topology in analytic applications. -/
def multiplicityRange (u : U) : Subrepresentation (secondRestriction tau) :=
  (multiplicityEvaluationAt tau rho u).range

abbrev MultiplicityRangeSpace (u : U) :=
  (multiplicityRange tau rho u).toSubmodule

/-- The second-factor action on the evaluation image. -/
def multiplicityRangeRepresentation (u : U) :
    Representation k H (MultiplicityRangeSpace tau rho u) :=
  (multiplicityRange tau rho u).toRepresentation

/-- Evaluation with codomain restricted to its invariant range. -/
def multiplicityToRange (u : U) :
    Representation.IntertwiningMap
      (multiplicityRepresentation tau rho)
      (multiplicityRangeRepresentation tau rho u) where
  toLinearMap :=
    { toFun := fun f => ⟨f u, ⟨f, rfl⟩⟩
      map_add' := fun f f' => by ext; simp
      map_smul' := fun a f => by ext; simp }
  isIntertwining' h := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    rfl

@[simp]
theorem multiplicityToRange_apply_coe (u : U)
    (f : MultiplicitySpace tau rho) :
    ((multiplicityToRange tau rho u f : MultiplicityRangeSpace tau rho u) : T) =
      f u :=
  rfl

theorem multiplicityToRange_surjective (u : U) :
    Function.Surjective (multiplicityToRange tau rho u) := by
  intro y
  obtain ⟨f, hf⟩ := y.prop
  refine ⟨f, ?_⟩
  apply Subtype.ext
  exact hf

/-- At a nonzero first-factor vector, the abstract multiplicity
representation is equivalent to its concrete evaluation image. -/
def multiplicityRangeEquiv
    [Representation.IsIrreducible rho]
    {u : U} (hu : u ≠ 0) :
    Representation.Equiv
      (multiplicityRepresentation tau rho)
      (multiplicityRangeRepresentation tau rho u) :=
  Representation.IntertwiningMap.ofBijective
    (multiplicityToRange tau rho u)
    ⟨fun _ _ h => multiplicityEvaluationAt_injective tau rho hu
        (congrArg Subtype.val h),
      multiplicityToRange_surjective tau rho u⟩

/-- Semisimplicity of the second-factor restriction descends to the
multiplicity representation. -/
theorem multiplicityRepresentation_isSemisimple
    [Representation.IsIrreducible rho]
    {u : U} (hu : u ≠ 0)
    (hSemisimple : Representation.IsSemisimpleRepresentation
      (secondRestriction tau)) :
    Representation.IsSemisimpleRepresentation
      (multiplicityRepresentation tau rho) := by
  let : IsSemisimpleModule k[H] (secondRestriction tau).asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule
      (secondRestriction tau)).mp hSemisimple
  let evaluationAsModule :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (multiplicityRepresentation tau rho) (secondRestriction tau))
      (multiplicityEvaluationAt tau rho u)
  let : IsSemisimpleModule k[H]
      (multiplicityRepresentation tau rho).asModule :=
    IsSemisimpleModule.of_injective evaluationAsModule
      (multiplicityEvaluationAt_injective tau rho hu)
  exact
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule
      (multiplicityRepresentation tau rho)).mpr inferInstance

/-- Evaluation on a vector and an intertwiner, linearized through the tensor
product. -/
def multiplicityEvaluationLinear :
    U ⊗[k] MultiplicitySpace tau rho →ₗ[k] T :=
  TensorProduct.lift
    { toFun := fun u =>
        { toFun := fun f => f u
          map_add' := fun f f' => by simp
          map_smul' := fun a f => by simp }
      map_add' := by
        intro u u'
        ext f
        simp
      map_smul' := by
        intro a u
        ext f
        simp }

@[simp]
theorem multiplicityEvaluationLinear_tmul
    (u : U) (f : MultiplicitySpace tau rho) :
    multiplicityEvaluationLinear tau rho (u ⊗ₜ[k] f) = f u :=
  rfl

/-- Evaluation is equivariant for the first factor. -/
def multiplicityEvaluationFirst :
    Representation.IntertwiningMap
      (rho.tprod (1 : Representation k G (MultiplicitySpace tau rho)))
      (firstRestriction tau) where
  toLinearMap := multiplicityEvaluationLinear tau rho
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro u f
    simp [Representation.IntertwiningMap.isIntertwining]

/-- Evaluation is equivariant for the full product action. -/
def multiplicityEvaluation :
    Representation.IntertwiningMap
      (externalTprod rho (multiplicityRepresentation tau rho)) tau where
  toLinearMap := multiplicityEvaluationLinear tau rho
  isIntertwining' gh := by
    apply TensorProduct.ext'
    intro u f
    rcases gh with ⟨g, h⟩
    simp only [LinearMap.comp_apply, externalTprod_tmul,
      multiplicityRepresentation_apply, multiplicityEvaluationLinear_tmul]
    rw [f.isIntertwining]
    change tau (1, h) (tau (g, 1) (f u)) = tau (g, h) (f u)
    rw [← Module.End.mul_apply, ← map_mul]
    simp

@[simp]
theorem multiplicityEvaluation_apply_tmul
    (u : U) (f : MultiplicitySpace tau rho) :
    multiplicityEvaluation tau rho (u ⊗ₜ[k] f) = f u :=
  rfl

/-!
## Injectivity of evaluation
-/

variable {M : Type*} [AddCommGroup M] [Module k M]

/-- A rank-one operator on the first tensor factor extracts one coefficient
in the basis expansion of a tensor. -/
theorem map_rankOne_id_eq_tmul_coordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k U) (i : ι) (u : U) (x : U ⊗[k] M) :
    TensorProduct.map (rankOne b i u) LinearMap.id x =
      u ⊗ₜ[k] (TensorProduct.equivFinsuppOfBasisLeft b x i) := by
  induction x <;>
    simp_all [rankOne,
      TensorProduct.smul_tmul, TensorProduct.tmul_smul,
      TensorProduct.tmul_add]

variable [IsAlgClosed k] [FiniteDimensional k U]

omit [IsAlgClosed k] [FiniteDimensional k U] in
/-- Evaluation commutes with the linear extension of the first-factor
action to the group algebra. -/
theorem multiplicityEvaluationLinear_map_asAlgebraHom
    (r : k[G]) (x : U ⊗[k] MultiplicitySpace tau rho) :
    multiplicityEvaluationLinear tau rho
        (TensorProduct.map (rho.asAlgebraHom r) LinearMap.id x) =
      (firstRestriction tau).asAlgebraHom r
        (multiplicityEvaluationLinear tau rho x) := by
  apply MonoidAlgebra.induction_on r
  · intro g
    simp only [Representation.asAlgebraHom_of]
    change
      multiplicityEvaluationFirst tau rho
          (TensorProduct.map (rho g) LinearMap.id x) =
        firstRestriction tau g (multiplicityEvaluationFirst tau rho x)
    simpa [LinearMap.comp_apply, Representation.tprod_apply,
      Module.End.one_eq_id] using
      LinearMap.congr_fun
        ((multiplicityEvaluationFirst tau rho).isIntertwining' g) x
  · intro r s hr hs
    simp only [map_add, TensorProduct.map_add_left, LinearMap.add_apply]
    rw [hr, hs]
  · intro a r hr
    simp only [map_smul, TensorProduct.map_smul_left, LinearMap.smul_apply]
    rw [hr]

/-- Burnside's theorem makes the canonical evaluation map injective when
the first-factor representation is irreducible. -/
theorem multiplicityEvaluationLinear_injective
    [Representation.IsIrreducible rho] :
    Function.Injective (multiplicityEvaluationLinear tau rho) := by
  intro x y hxy
  suffices hzero : ∀ z, multiplicityEvaluationLinear tau rho z = 0 → z = 0 by
    apply sub_eq_zero.mp
    apply hzero (x - y)
    simpa using congrArg
      (fun z => z - multiplicityEvaluationLinear tau rho y) hxy
  intro x hx
  let b := Module.finBasis k U
  let c := TensorProduct.equivFinsuppOfBasisLeft b x
  have hc : c = 0 := by
    apply Finsupp.ext
    intro i
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro u
    obtain ⟨r, hr⟩ := representation_asAlgebraHom_surjective rho (rankOne b i u)
    have hmap := multiplicityEvaluationLinear_map_asAlgebraHom
      (tau := tau) (rho := rho) r x
    rw [hx, map_zero] at hmap
    rw [hr, map_rankOne_id_eq_tmul_coordinate] at hmap
    change c i u = 0 at hmap
    simpa using hmap
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  change c = 0
  exact hc

omit [IsAlgClosed k] [FiniteDimensional k U] in
/-- A nonzero copy of `rho` in the first-factor restriction makes evaluation
surjective whenever the product representation is irreducible. -/
theorem multiplicityEvaluation_surjective
    [Representation.IsIrreducible tau]
    (hOccurs : ∃ f : MultiplicitySpace tau rho, f ≠ 0) :
    Function.Surjective (multiplicityEvaluation tau rho) := by
  have hEvaluation : multiplicityEvaluation tau rho ≠ 0 := by
    obtain ⟨f, hf⟩ := hOccurs
    have hu : ∃ u : U, f u ≠ 0 := by
      by_contra h
      push Not at h
      apply hf
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro u
      simpa using h u
    obtain ⟨u, hu⟩ := hu
    intro hzero
    have happ := congrArg
      (fun q : Representation.IntertwiningMap
          (externalTprod rho (multiplicityRepresentation tau rho)) tau =>
        q (u ⊗ₜ[k] f)) hzero
    exact hu (by simpa using happ)
  exact
    (Representation.IsIrreducible.surjective_or_eq_zero
      (ρ := tau) (multiplicityEvaluation tau rho)).resolve_right hEvaluation

/-- The canonical evaluation is an equivalence once `rho` occurs in an
irreducible product representation. -/
def multiplicityEvaluationEquiv
    [Representation.IsIrreducible rho]
    [Representation.IsIrreducible tau]
    (hOccurs : ∃ f : MultiplicitySpace tau rho, f ≠ 0) :
    Representation.Equiv
      (externalTprod rho (multiplicityRepresentation tau rho)) tau :=
  Representation.IntertwiningMap.ofBijective
    (multiplicityEvaluation tau rho)
    ⟨multiplicityEvaluationLinear_injective tau rho,
      multiplicityEvaluation_surjective tau rho hOccurs⟩

@[simp]
theorem multiplicityEvaluationEquiv_apply_tmul
    [Representation.IsIrreducible rho]
    [Representation.IsIrreducible tau]
    (hOccurs : ∃ f : MultiplicitySpace tau rho, f ≠ 0)
    (u : U) (f : MultiplicitySpace tau rho) :
    multiplicityEvaluationEquiv tau rho hOccurs (u ⊗ₜ[k] f) = f u :=
  rfl

/-!
## Irreducibility transported through equivalence
-/

omit [IsAlgClosed k] in
theorem isIrreducible_of_equiv
    {K X Y : Type*} [Group K]
    [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y]
    {pi : Representation k K X} {pi' : Representation k K Y}
    [Representation.IsIrreducible pi']
    (e : Representation.Equiv pi pi') :
    Representation.IsIrreducible pi := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  let f := Representation.IntertwiningMap.equivLinearMapAsModule pi pi'
    e.toIntertwiningMap
  let em : pi.asModule ≃ₗ[k[K]] pi'.asModule :=
    LinearEquiv.ofBijective f e.toLinearEquiv.bijective
  exact IsSimpleModule.congr em

variable {W : Type*} [AddCommGroup W] [Module k W]
variable (sigma : Representation k H W)

/-- An endomorphism of the second factor induces an endomorphism of the
external tensor product. -/
def externalTprodRightEnd
    (f : Representation.IntertwiningMap sigma sigma) :
    Representation.IntertwiningMap
      (externalTprod rho sigma) (externalTprod rho sigma) where
  toLinearMap := TensorProduct.map LinearMap.id f.toLinearMap
  isIntertwining' gh := by
    apply TensorProduct.ext'
    intro u w
    rcases gh with ⟨g, h⟩
    simp only [LinearMap.comp_apply, externalTprod_tmul,
      TensorProduct.map_tmul, LinearMap.id_apply]
    change rho g u ⊗ₜ[k] f (sigma h w) =
      rho g u ⊗ₜ[k] sigma h (f w)
    rw [f.isIntertwining]

omit [IsAlgClosed k] [FiniteDimensional k U] in
@[simp]
theorem externalTprodRightEnd_apply_tmul
    (f : Representation.IntertwiningMap sigma sigma) (u : U) (w : W) :
    externalTprodRightEnd rho sigma f (u ⊗ₜ[k] w) = u ⊗ₜ[k] f w :=
  rfl

/-- If the external tensor product is irreducible, every endomorphism of the
second factor is scalar. -/
theorem secondFactor_end_eq_smul_one
    [Nontrivial U] [FiniteDimensional k W]
    [Representation.IsIrreducible (externalTprod rho sigma)]
    (f : Representation.IntertwiningMap sigma sigma) :
    ∃ c : k, f = c • 1 := by
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := externalTprod rho sigma)).2 (externalTprodRightEnd rho sigma f)
  refine ⟨c, ?_⟩
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro w
  let b := Module.finBasis k U
  have hdim : 0 < Module.finrank k U := Module.finrank_pos
  let i : Fin (Module.finrank k U) := ⟨0, hdim⟩
  have happ := congrArg
    (fun q : Representation.IntertwiningMap
        (externalTprod rho sigma) (externalTprod rho sigma) =>
      q (b i ⊗ₜ[k] w)) hc.symm
  have hcoord := congrArg
    (fun x : U ⊗[k] W =>
      TensorProduct.equivFinsuppOfBasisLeft b x i) happ
  simpa [externalTprodRightEnd_apply_tmul,
    Representation.IntertwiningMap.smul_apply] using hcoord

omit [IsAlgClosed k] in
/-- Complements in the subrepresentation lattice are also complements of
the underlying linear subspaces. -/
theorem isCompl_toSubmodule
    {K X : Type*} [Group K] [AddCommGroup X] [Module k X]
    {pi : Representation k K X} {S C : Subrepresentation pi}
    (h : IsCompl S C) : IsCompl S.toSubmodule C.toSubmodule := by
  constructor
  · rw [disjoint_iff]
    change S.toSubmodule ⊓ C.toSubmodule =
      (⊥ : Subrepresentation pi).toSubmodule
    have hInf : S ⊓ C = ⊥ := disjoint_iff.mp h.disjoint
    exact congrArg Subrepresentation.toSubmodule hInf
  · rw [codisjoint_iff]
    change S.toSubmodule ⊔ C.toSubmodule =
      (⊤ : Subrepresentation pi).toSubmodule
    have hSup : S ⊔ C = ⊤ := codisjoint_iff.mp h.codisjoint
    exact congrArg Subrepresentation.toSubmodule hSup

omit [IsAlgClosed k] in
/-- A nonzero semisimple representation with scalar endomorphism commutant is
irreducible. -/
theorem isIrreducible_of_semisimple_of_scalar_commutant
    {K X : Type*} [Group K]
    [AddCommGroup X] [Module k X] [Nontrivial X]
    (pi : Representation k K X)
    (hSemisimple : Representation.IsSemisimpleRepresentation pi)
    (hScalar : ∀ f : Representation.IntertwiningMap pi pi,
      ∃ c : k, f = c • 1) :
    Representation.IsIrreducible pi := by
  let : Representation.IsSemisimpleRepresentation pi := hSemisimple
  let : Nontrivial (Subrepresentation pi) :=
    ⟨⟨⊥, ⊤, by
      intro h
      exact (bot_ne_top : (⊥ : Submodule k X) ≠ ⊤)
        (congrArg Subrepresentation.toSubmodule h)⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  obtain ⟨C, hCompl⟩ := exists_isCompl S
  have hLinearCompl : IsCompl S.toSubmodule C.toSubmodule :=
    isCompl_toSubmodule hCompl
  let p : Representation.IntertwiningMap pi pi :=
    { toLinearMap := S.toSubmodule.projection C.toSubmodule hLinearCompl
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        have hx : x ∈ S.toSubmodule ⊔ C.toSubmodule := by
          rw [hLinearCompl.codisjoint.eq_top]
          exact Submodule.mem_top
        rw [Submodule.mem_sup] at hx
        obtain ⟨s, hs, c, hc, rfl⟩ := hx
        have hgs := S.apply_mem_toSubmodule g hs
        have hgc := C.apply_mem_toSubmodule g hc
        simp only [LinearMap.comp_apply, map_add]
        rw [S.toSubmodule.projection_apply_of_mem_left hLinearCompl hgs,
          S.toSubmodule.projection_apply_of_mem_right hLinearCompl hgc,
          S.toSubmodule.projection_apply_of_mem_left hLinearCompl hs,
          S.toSubmodule.projection_apply_of_mem_right hLinearCompl hc]
        simp }
  obtain ⟨a, hp⟩ := hScalar p
  have hCbot : C.toSubmodule = ⊥ := by
    by_contra hC
    have hSSub : S.toSubmodule ≠ ⊥ := by
      intro hSbot
      apply hS
      apply Subrepresentation.ext
      exact hSbot
    obtain ⟨s, hs, hs0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot hSSub
    obtain ⟨c, hc, hc0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot hC
    have hcScalar := congrArg
      (fun f : Representation.IntertwiningMap pi pi => f c) hp
    have ha : a = 0 := by
      have hac : a • c = 0 := by
        simpa [p, S.toSubmodule.projection_apply_of_mem_right
          hLinearCompl hc] using hcScalar.symm
      exact (smul_eq_zero.mp hac).resolve_right hc0
    have hsScalar := congrArg
      (fun f : Representation.IntertwiningMap pi pi => f s) hp
    have : s = 0 := by
      simpa [p, ha, S.toSubmodule.projection_apply_of_mem_left
        hLinearCompl hs] using hsScalar
    exact hs0 this
  have hCrep : C = ⊥ := by
    apply Subrepresentation.ext
    exact hCbot
  have htop := hCompl.codisjoint.eq_top
  rw [hCrep] at htop
  calc
    S = S ⊔ ⊥ := (sup_eq_left.mpr bot_le).symm
    _ = ⊤ := htop

/-- For an irreducible product representation, the canonical multiplicity
representation is irreducible as soon as the second-factor restriction is
semisimple. -/
theorem multiplicityRepresentation_isIrreducible
    [Nontrivial U] [FiniteDimensional k T]
    [Representation.IsIrreducible rho]
    [Representation.IsIrreducible tau]
    (hOccurs : ∃ f : MultiplicitySpace tau rho, f ≠ 0)
    (hSemisimple : Representation.IsSemisimpleRepresentation
      (secondRestriction tau)) :
    Representation.IsIrreducible (multiplicityRepresentation tau rho) := by
  obtain ⟨f, hf⟩ := hOccurs
  let : Nontrivial (MultiplicitySpace tau rho) :=
    ⟨⟨f, 0, hf⟩⟩
  obtain ⟨u, hu⟩ := exists_ne (0 : U)
  have hMultiplicitySemisimple :=
    multiplicityRepresentation_isSemisimple tau rho hu hSemisimple
  let : Representation.IsIrreducible
      (externalTprod rho (multiplicityRepresentation tau rho)) :=
    isIrreducible_of_equiv
      (multiplicityEvaluationEquiv tau rho ⟨f, hf⟩)
  exact isIrreducible_of_semisimple_of_scalar_commutant
    (multiplicityRepresentation tau rho) hMultiplicitySemisimple
    (secondFactor_end_eq_smul_one rho (multiplicityRepresentation tau rho))

/-- The ambient evaluation-image realization of the multiplicity factor is
irreducible under the same hypotheses. -/
theorem multiplicityRangeRepresentation_isIrreducible
    [Nontrivial U] [FiniteDimensional k T]
    [Representation.IsIrreducible rho]
    [Representation.IsIrreducible tau]
    {u : U} (hu : u ≠ 0)
    (hOccurs : ∃ f : MultiplicitySpace tau rho, f ≠ 0)
    (hSemisimple : Representation.IsSemisimpleRepresentation
      (secondRestriction tau)) :
    Representation.IsIrreducible
      (multiplicityRangeRepresentation tau rho u) := by
  let : Representation.IsIrreducible
      (multiplicityRepresentation tau rho) :=
    multiplicityRepresentation_isIrreducible tau rho hOccurs hSemisimple
  exact isIrreducible_of_equiv (multiplicityRangeEquiv tau rho hu).symm

/-!
## Extracting a factor from a semisimple restriction
-/

/-- A group-algebra submodule of the first-factor restriction, regarded as a
representation of the first group. -/
def firstSubmoduleRepresentation
    (S : Submodule k[G] (firstRestriction tau).asModule) :
    Representation k G S :=
  Representation.ofModule' S

/-- The same first-factor constituent, now realized as an invariant subspace
of the ambient restriction. -/
def firstSubmoduleAsSubrepresentation
    (S : Submodule k[G] (firstRestriction tau).asModule) :
    Subrepresentation (firstRestriction tau) :=
  Subrepresentation.ofSubmodule' S

/-- Converting a group-algebra module to a representation and back recovers
the original module.  This is the concrete module equivalence needed for the
submodule inclusion below. -/
def ofModulePrimeAsModuleEquiv
    (S : Type*) [AddCommGroup S] [Module k S] [Module k[G] S]
    [IsScalarTower k k[G] S] :
    (Representation.ofModule' (k := k) (G := G) S).asModule ≃ₗ[k[G]] S where
  toFun s := s
  invFun s := s
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r s := by
    show
      (Representation.ofModule' (k := k) (G := G) S).asAlgebraHom r s =
        r • (show S from s)
    simp [Representation.asAlgebraHom, Representation.ofModule']

/-- The abstract group-algebra subtype and the ambient invariant-subspace
subtype carry equivalent first-factor representations. -/
def firstSubmoduleAmbientMap
    (S : Submodule k[G] (firstRestriction tau).asModule) :
    Representation.IntertwiningMap
      (firstSubmoduleRepresentation tau S)
      (firstSubmoduleAsSubrepresentation tau S).toRepresentation where
  toLinearMap :=
    { toFun := fun s => ⟨s.1, s.2⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  isIntertwining' g := by
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    change
      ((MonoidAlgebra.single g (1 : k)) •
          (s : (firstRestriction tau).asModule) : T) =
        firstRestriction tau g s.1
    rw [Representation.single_smul, one_smul]
    rfl

def firstSubmoduleAmbientEquiv
    (S : Submodule k[G] (firstRestriction tau).asModule) :
    Representation.Equiv
      (firstSubmoduleRepresentation tau S)
      (firstSubmoduleAsSubrepresentation tau S).toRepresentation :=
  Representation.IntertwiningMap.ofBijective
    (firstSubmoduleAmbientMap tau S)
    ⟨fun _ _ h => Subtype.ext (congrArg Subtype.val h), fun y =>
      ⟨⟨y.1, y.2⟩, Subtype.ext rfl⟩⟩

omit [IsAlgClosed k] in
/-- A simple first-factor group-algebra submodule is irreducible in its
ambient invariant-subspace realization. -/
theorem firstSubmoduleAsSubrepresentation_isIrreducible
    (S : Submodule k[G] (firstRestriction tau).asModule)
    (hS : IsSimpleModule k[G] S) :
    Representation.IsIrreducible
      (firstSubmoduleAsSubrepresentation tau S).toRepresentation := by
  let : IsSimpleModule k[G] S := hS
  let : IsSimpleModule k[G]
      (firstSubmoduleRepresentation tau S).asModule :=
    IsSimpleModule.congr (ofModulePrimeAsModuleEquiv S)
  let : Representation.IsIrreducible
      (firstSubmoduleRepresentation tau S) :=
    (Representation.irreducible_iff_isSimpleModule_asModule
      (firstSubmoduleRepresentation tau S)).mpr inferInstance
  exact isIrreducible_of_equiv (firstSubmoduleAmbientEquiv tau S).symm

/-- The tautological inclusion of a first-factor submodule. -/
def firstSubmoduleInclusion
    (S : Submodule k[G] (firstRestriction tau).asModule) :
    Representation.IntertwiningMap
      (firstSubmoduleRepresentation tau S) (firstRestriction tau) :=
  (Representation.IntertwiningMap.equivLinearMapAsModule
    (firstSubmoduleRepresentation tau S) (firstRestriction tau)).symm
      (S.subtype.comp (ofModulePrimeAsModuleEquiv S).toLinearMap)

omit [IsAlgClosed k] in
theorem firstSubmoduleInclusion_injective
    (S : Submodule k[G] (firstRestriction tau).asModule) :
    Function.Injective (firstSubmoduleInclusion tau S) := by
  intro x y hxy
  apply (ofModulePrimeAsModuleEquiv (k := k) (G := G) S).injective
  apply S.subtype_injective
  exact hxy

omit [IsAlgClosed k] in
/-- A nonzero semisimple first-factor restriction contains a simple
submodule. -/
theorem exists_simple_firstSubmodule
    [Nontrivial T]
    (hSemisimple : Representation.IsSemisimpleRepresentation
      (firstRestriction tau)) :
    ∃ S : Submodule k[G] (firstRestriction tau).asModule,
      IsSimpleModule k[G] S := by
  let : IsSemisimpleModule k[G] (firstRestriction tau).asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule
      (firstRestriction tau)).mp hSemisimple
  let : Nontrivial (firstRestriction tau).asModule := by
    exact (firstRestriction tau).asModuleEquiv.toEquiv.nontrivial
  exact IsSemisimpleModule.exists_simple_submodule
    k[G] (firstRestriction tau).asModule

/-- If an irreducible product representation has semisimple restriction to
the first factor, it is equivalent to the external tensor product of a simple
first-factor constituent and its canonical multiplicity representation. -/
theorem exists_externalTprod_equiv_of_firstRestriction_semisimple
    [FiniteDimensional k T] [Nontrivial T]
    [Representation.IsIrreducible tau]
    (hSemisimple : Representation.IsSemisimpleRepresentation
      (firstRestriction tau)) :
    ∃ S : Submodule k[G] (firstRestriction tau).asModule,
      IsSimpleModule k[G] S ∧
        Nonempty
          (Representation.Equiv
            (externalTprod
              (firstSubmoduleRepresentation tau S)
              (multiplicityRepresentation tau
                (firstSubmoduleRepresentation tau S)))
            tau) := by
  obtain ⟨S, hS⟩ := exists_simple_firstSubmodule tau hSemisimple
  let : IsSimpleModule k[G] S := hS
  let : Nontrivial S := IsSimpleModule.nontrivial k[G] S
  let : IsSimpleModule k[G]
      (firstSubmoduleRepresentation tau S).asModule :=
    IsSimpleModule.congr (ofModulePrimeAsModuleEquiv S)
  let : Representation.IsIrreducible
      (firstSubmoduleRepresentation tau S) :=
    (Representation.irreducible_iff_isSimpleModule_asModule
      (firstSubmoduleRepresentation tau S)).mpr inferInstance
  let : FiniteDimensional k S :=
    FiniteDimensional.of_injective
      (firstSubmoduleInclusion tau S).toLinearMap
      (firstSubmoduleInclusion_injective tau S)
  have hInclusion : firstSubmoduleInclusion tau S ≠ 0 := by
    intro hzero
    obtain ⟨x, y, hxy⟩ := exists_pair_ne S
    apply hxy
    apply firstSubmoduleInclusion_injective tau S
    rw [hzero]
    rfl
  refine ⟨S, hS, ?_⟩
  exact ⟨multiplicityEvaluationEquiv tau (firstSubmoduleRepresentation tau S)
    ⟨firstSubmoduleInclusion tau S, hInclusion⟩⟩

/-- An irreducible product representation whose two factor restrictions are
semisimple is an external tensor product of irreducible factor
representations. -/
theorem exists_irreducible_externalTprod_equiv_of_restrictions_semisimple
    [FiniteDimensional k T] [Nontrivial T]
    [Representation.IsIrreducible tau]
    (hFirstSemisimple : Representation.IsSemisimpleRepresentation
      (firstRestriction tau))
    (hSecondSemisimple : Representation.IsSemisimpleRepresentation
      (secondRestriction tau)) :
    ∃ S : Submodule k[G] (firstRestriction tau).asModule,
      IsSimpleModule k[G] S ∧
        Representation.IsIrreducible
          (firstSubmoduleRepresentation tau S) ∧
        Representation.IsIrreducible
          (multiplicityRepresentation tau
            (firstSubmoduleRepresentation tau S)) ∧
        Nonempty
          (Representation.Equiv
            (externalTprod
              (firstSubmoduleRepresentation tau S)
              (multiplicityRepresentation tau
                (firstSubmoduleRepresentation tau S)))
            tau) := by
  obtain ⟨S, hS, hEquiv⟩ :=
    exists_externalTprod_equiv_of_firstRestriction_semisimple
      tau hFirstSemisimple
  let : IsSimpleModule k[G] S := hS
  let : Nontrivial S := IsSimpleModule.nontrivial k[G] S
  let : IsSimpleModule k[G]
      (firstSubmoduleRepresentation tau S).asModule :=
    IsSimpleModule.congr (ofModulePrimeAsModuleEquiv S)
  let : Representation.IsIrreducible
      (firstSubmoduleRepresentation tau S) :=
    (Representation.irreducible_iff_isSimpleModule_asModule
      (firstSubmoduleRepresentation tau S)).mpr inferInstance
  let : FiniteDimensional k S :=
    FiniteDimensional.of_injective
      (firstSubmoduleInclusion tau S).toLinearMap
      (firstSubmoduleInclusion_injective tau S)
  have hInclusion : firstSubmoduleInclusion tau S ≠ 0 := by
    intro hzero
    obtain ⟨x, y, hxy⟩ := exists_pair_ne S
    apply hxy
    apply firstSubmoduleInclusion_injective tau S
    rw [hzero]
    rfl
  have hMultiplicityIrreducible :
      Representation.IsIrreducible
        (multiplicityRepresentation tau
          (firstSubmoduleRepresentation tau S)) :=
    multiplicityRepresentation_isIrreducible tau
      (firstSubmoduleRepresentation tau S)
      ⟨firstSubmoduleInclusion tau S, hInclusion⟩ hSecondSemisimple
  exact ⟨S, hS, inferInstance, hMultiplicityIrreducible, hEquiv⟩

end

end ProductFactorization
end Math
