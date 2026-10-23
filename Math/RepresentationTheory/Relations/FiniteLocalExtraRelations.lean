import Math.RepresentationTheory.Coefficients.FiniteLocalRelationCompleteness
import Math.RepresentationTheory.Coefficients.RelationInputExtension

/-! Additional source relations in the published finite-local/statistical coordinates.
The input map is computed from contractions, not from an assumed annihilator match. -/
namespace Math.FiniteLocalExtraRelations
set_option autoImplicit false
noncomputable section
open Representation FiniteLocalRelationCompleteness
open scoped TensorProduct
variable {G H A X I J : Type*} [Group G] [Group H] [Fintype I] [DecidableEq I]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup X] [Module ℂ X]
  (a : Representation ℂ G A) (x : Representation ℂ H X)
  (p : I → IntertwiningMap a (trivial ℂ G ℂ)) (v : I → A)
  (hv : ∀ i j, p i (v j) = if i = j then 1 else 0)
  (hp : ∀ f : IntertwiningMap a (trivial ℂ G ℂ), f = ∑ i, f (v i) • p i)
  (localExchange : J → Representation.Equiv a a)
  (flavorExchange : J → Representation.Equiv x x) (sign : J → ℂ)

abbrev Coefficient := StatisticalCompleteness.sector
  (FiniteStatisticalFactor.sourceAction a x localExchange flavorExchange) sign

abbrev CoordinateInput := (I →₀ X) ⧸ relations a x p v localExchange flavorExchange sign

def values : Coefficient a x localExchange flavorExchange sign →ₗ[ℂ] ((A ⊗[ℂ] X) →ₗ[ℂ] ℂ) where
  toFun f := f.val.toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coordinates : (A ⊗[ℂ] X) →ₗ[ℂ] (I →₀ X) := TensorProduct.lift {
  toFun u := ∑ i, p i u • Finsupp.lsingle i
  map_add' u w := by simp only [map_add, add_smul, Finset.sum_add_distrib]
  map_smul' c u := by simp only [map_smul, smul_eq_mul, smul_smul, Finset.smul_sum, RingHom.id_apply] }

omit [DecidableEq I] in
@[simp] theorem coordinates_tmul (u : A) (w : X) :
    coordinates a p (u ⊗ₜ[ℂ] w) = ∑ i, Finsupp.single i (p i u • w) := by
  simp [coordinates, LinearMap.sum_apply, Finsupp.smul_single]

def inputMap : (A ⊗[ℂ] X) →ₗ[ℂ] CoordinateInput a x p v localExchange flavorExchange sign :=
  (relations a x p v localExchange flavorExchange sign).mkQ.comp (coordinates a p)

omit [DecidableEq I] in
@[simp] theorem inputMap_tmul (u : A) (w : X) :
    inputMap a x p v localExchange flavorExchange sign (u ⊗ₜ[ℂ] w) =
      ∑ i, p i u • (relations a x p v localExchange flavorExchange sign).mkQ (Finsupp.single i w) := by
  simp only [inputMap, LinearMap.comp_apply, coordinates_tmul, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finsupp.smul_single, map_smul]

include hv hp in
theorem evaluation (f : Coefficient a x localExchange flavorExchange sign) (u : A ⊗[ℂ] X) :
    FiniteLocalRelationCompleteness.equiv a x p v hv hp localExchange flavorExchange sign f
      (inputMap a x p v localExchange flavorExchange sign u) = values a x localExchange flavorExchange sign f u := by
  induction u using TensorProduct.inductionOn with
  | add u w hu hw => simp only [map_add, hu, hw]
  | tmul u w =>
    rw [inputMap_tmul, map_sum]
    have h := FiniteLocalRelationCompleteness.reconstruction a x p v hv hp localExchange flavorExchange sign
      (FiniteLocalRelationCompleteness.equiv a x p v hv hp localExchange flavorExchange sign f) u w
    change (∑ i, FiniteLocalRelationCompleteness.equiv a x p v hv hp localExchange flavorExchange sign f
      (p i u • (relations a x p v localExchange flavorExchange sign).mkQ (Finsupp.single i w))) = f.val (u ⊗ₜ[ℂ] w)
    simpa only [LinearEquiv.symm_apply_apply, map_smul, smul_eq_mul] using h.symm

abbrev sourceAction : Representation ℂ H (A ⊗[ℂ] X) := (trivial ℂ H A).tprod x

omit [DecidableEq I] in
theorem inputMap_covariant (h : H) (u : A ⊗[ℂ] X) :
    inputMap a x p v localExchange flavorExchange sign (sourceAction x h u) =
      residualRepresentation a x p v localExchange flavorExchange sign h
        (inputMap a x p v localExchange flavorExchange sign u) := by
  induction u using TensorProduct.inductionOn with
  | add u w hu hw => simp only [map_add, hu, hw]
  | tmul u w =>
    simp [sourceAction, Representation.tprod_apply, inputMap_tmul,
      residualRepresentation, ResidualRelationPresentation.quotientRepresentation]

variable (T : Submodule ℂ (A ⊗[ℂ] X))
  (hT : ∀ h, T ≤ T.comap (sourceAction x h))

abbrev Input := RelationInputExtension.Input (values a x localExchange flavorExchange sign) T
abbrev extraRelations := T.map (inputMap a x p v localExchange flavorExchange sign)

omit [DecidableEq I] in
include hT in
theorem extra_stable : ∀ h, extraRelations a x p v localExchange flavorExchange sign T ≤
    (extraRelations a x p v localExchange flavorExchange sign T).comap
      (residualRepresentation a x p v localExchange flavorExchange sign h) := by
  rintro h _ ⟨u, hu, rfl⟩
  exact ⟨sourceAction x h u, hT h hu, inputMap_covariant a x p v localExchange flavorExchange sign h u⟩

abbrev residual := (residualRepresentation a x p v localExchange flavorExchange sign).quotient
  (extraRelations a x p v localExchange flavorExchange sign T)
  (extra_stable a x p v localExchange flavorExchange sign T hT)

def equiv := RelationInputExtension.equiv
  (residualRepresentation a x p v localExchange flavorExchange sign) (trivial ℂ H ℂ)
  (FiniteLocalRelationCompleteness.equiv a x p v hv hp localExchange flavorExchange sign)
  (inputMap a x p v localExchange flavorExchange sign) (values a x localExchange flavorExchange sign)
  (evaluation a x p v hv hp localExchange flavorExchange sign) T
  (extra_stable a x p v localExchange flavorExchange sign T hT)

@[simp] theorem extraction (f : Input a x localExchange flavorExchange sign T) (u : A ⊗[ℂ] X) :
    equiv a x p v hv hp localExchange flavorExchange sign T hT f
      ((extraRelations a x p v localExchange flavorExchange sign T).mkQ
        (inputMap a x p v localExchange flavorExchange sign u)) = f.val.val u :=
  RelationInputExtension.extraction _ _ _ _ _ _ _ _ _ _

@[simp] theorem reconstruction (f : IntertwiningMap
    (residual a x p v localExchange flavorExchange sign T hT) (trivial ℂ H ℂ)) (u : A ⊗[ℂ] X) :
    ((equiv a x p v hv hp localExchange flavorExchange sign T hT).symm f).val.val u =
      f ((extraRelations a x p v localExchange flavorExchange sign T).mkQ
        (inputMap a x p v localExchange flavorExchange sign u)) :=
  by
    change values a x localExchange flavorExchange sign _ u = _
    exact RelationInputExtension.reconstruction _ _ _ _ _ _ _ _ f u

@[simp] theorem reconstruction_tmul (f : IntertwiningMap
    (residual a x p v localExchange flavorExchange sign T hT) (trivial ℂ H ℂ)) (u : A) (w : X) :
    ((equiv a x p v hv hp localExchange flavorExchange sign T hT).symm f).val.val (u ⊗ₜ[ℂ] w) =
      ∑ i, p i u * f ((extraRelations a x p v localExchange flavorExchange sign T).mkQ
        ((relations a x p v localExchange flavorExchange sign).mkQ (Finsupp.single i w))) := by
  rw [reconstruction, inputMap_tmul, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- The existing coefficient type is recovered when no constraint is added. -/
def emptyEquiv : Input a x localExchange flavorExchange sign (⊥ : Submodule ℂ (A ⊗[ℂ] X)) ≃ₗ[ℂ]
    Coefficient a x localExchange flavorExchange sign :=
  RelationInputExtension.emptyEquiv (values a x localExchange flavorExchange sign)


include hv hp hT in
theorem nonzero_iff : (∃ f : Input a x localExchange flavorExchange sign T, f ≠ 0) ↔
    ∃ q : IntertwiningMap (residual a x p v localExchange flavorExchange sign T hT)
      (trivial ℂ H ℂ), q ≠ 0 :=
  RelationInputExtension.nonzero_iff _ _
    (FiniteLocalRelationCompleteness.equiv a x p v hv hp localExchange flavorExchange sign)
    _ _ (evaluation a x p v hv hp localExchange flavorExchange sign) _
    (extra_stable a x p v localExchange flavorExchange sign T hT)

section Generated
variable {K : Type*} [AddCommGroup K] [Module ℂ K]
  (current : Representation ℂ H K) (divergence : IntertwiningMap current (sourceAction (A := A) x))

theorem range_stable : ∀ h, divergence.toLinearMap.range ≤
    divergence.toLinearMap.range.comap (sourceAction x h) := by
  rintro h _ ⟨c, rfl⟩
  exact ⟨current h c, IntertwiningMap.isIntertwining _ _ divergence h c⟩

/-- Supply an actual equivariant divergence, not an independently guessed relation matrix. -/
def divergenceEquiv := equiv a x p v hv hp localExchange flavorExchange sign
  divergence.toLinearMap.range (range_stable x current divergence)

theorem divergence_admissible_iff (f : Coefficient a x localExchange flavorExchange sign) :
    f ∈ Input a x localExchange flavorExchange sign divergence.toLinearMap.range ↔
      ∀ c, f.val (divergence c) = 0 := by
  constructor
  · intro h c
    exact h ⟨c, rfl⟩
  · rintro h _ ⟨c, rfl⟩
    exact h c
end Generated

end
end Math.FiniteLocalExtraRelations
