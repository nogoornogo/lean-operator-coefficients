import Physics.StandardModel.Operators.Dipole.DipoleSMCoefficient
import Math.LinearAlgebra.Selection.SelectedCoefficientInputs
import Math.RepresentationTheory.Decomposition.CommonIrreducible

open Math

/-! Prescribed flavor selection and arbitrary-domain coefficient generation.
Both gauge channels are selected separately; no photon matching is implied. -/
namespace Physics.DipoleFlavorSelection
set_option autoImplicit false
noncomputable section
open Representation

variable {H A B : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  (a : Representation ℂ H A) (b : Representation ℂ H B)
  (mu : A) (electron : Module.Dual ℂ B)

def evaluation : IntertwiningMap a b →ₗ[ℂ] ℂ where
  toFun k := electron (k mu)
  map_add' k l := by simp
  map_smul' z k := by simp

def residualSelector : (IntertwiningMap a b × IntertwiningMap a b) →ₗ[ℂ] (ℂ × ℂ) where
  toFun k := (evaluation a b mu electron k.1, evaluation a b mu electron k.2)
  map_add' k l := by ext <;> simp
  map_smul' z k := by ext <;> simp

variable [FiniteDimensional ℂ B]

abbrev Coefficients := DipoleSMCoefficient.SectorB a b × DipoleSMCoefficient.SectorW a b

def selector : Coefficients a b →ₗ[ℂ] (ℂ × ℂ) :=
  (residualSelector a b mu electron).comp (DipoleSMCoefficient.equiv a b).toLinearMap

theorem allowed_iff : (∃ c : Coefficients a b, selector a b mu electron c ≠ 0) ↔
    ∃ k : IntertwiningMap a b, electron (k mu) ≠ 0 := by
  constructor
  · rintro ⟨c, hc⟩
    by_contra hn
    have hk : ∀ k : IntertwiningMap a b, electron (k mu) = 0 := by simpa using hn
    apply hc
    exact Prod.ext (hk _) (hk _)
  · rintro ⟨k, hk⟩
    refine ⟨(DipoleSMCoefficient.equiv a b).symm (k, 0), ?_⟩
    intro hc
    have he := congrArg Prod.fst hc
    change electron (((DipoleSMCoefficient.equiv a b)
      ((DipoleSMCoefficient.equiv a b).symm (k, 0))).1 mu) = 0 at he
    rw [LinearEquiv.apply_symm_apply] at he
    exact hk he

/-- Structural sufficiency: an actual equivariant flavor bridge with nonzero
selected matrix element. No assertion that a UV model realizes this bridge. -/
theorem allowed_of_bridge (k : IntertwiningMap a b) (hk : electron (k mu) ≠ 0) :
    ∃ c : Coefficients a b, selector a b mu electron c ≠ 0 :=
  (allowed_iff a b mu electron).mpr ⟨k,hk⟩

theorem coefficient_exists_iff_shares (ha : IsSemisimpleRepresentation a) :
    (∃ c : Coefficients a b, c ≠ 0) ↔ CommonIrreducible.Shares a b :=
  (DipoleSMCoefficient.exists_nonzero_iff a b).trans (CommonIrreducible.nonzero_iff a b ha)

omit [FiniteDimensional ℂ B] in
/-- A residual symmetry element separates the two prescribed flavor weights. -/
theorem evaluation_zero_of_distinct_weights (g : H) (alpha beta : ℂ)
    (hmu : a g mu = alpha • mu)
    (he : ∀ y : B, electron (b g y) = beta * electron y)
    (hne : alpha ≠ beta) (k : IntertwiningMap a b) : electron (k mu) = 0 := by
  have h := congrArg electron (IntertwiningMap.isIntertwining _ _ k g mu)
  rw [hmu, map_smul, map_smul, he] at h
  have hz : (alpha-beta) * electron (k mu) = 0 := by
    change alpha * electron (k mu) = beta * electron (k mu) at h
    linear_combination h
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

theorem forbidden_of_distinct_weights (g : H) (alpha beta : ℂ)
    (hmu : a g mu = alpha • mu)
    (he : ∀ y : B, electron (b g y) = beta * electron y)
    (hne : alpha ≠ beta) : ∀ c : Coefficients a b, selector a b mu electron c = 0 := by
  intro c
  exact Prod.ext (evaluation_zero_of_distinct_weights a b mu electron g alpha beta hmu he hne _)
    (evaluation_zero_of_distinct_weights a b mu electron g alpha beta hmu he hne _)

variable {X : Type*} (F : X → Coefficients a b)

theorem realized_iff : (∃ x, selector a b mu electron (F x) ≠ 0) ↔
    ¬ Set.range F ⊆ (LinearMap.ker (selector a b mu electron) : Set (Coefficients a b)) :=
  SelectedCoefficientInputs.exists_nonzero_iff _ F

theorem realized_of_surjective (hF : Function.Surjective F) :
    (∃ x, selector a b mu electron (F x) ≠ 0) ↔
      ∃ k : IntertwiningMap a b, electron (k mu) ≠ 0 := by
  rw [← allowed_iff a b mu electron]
  constructor
  · rintro ⟨x,hx⟩; exact ⟨F x,hx⟩
  · rintro ⟨c,hc⟩
    obtain ⟨x,rfl⟩ := hF c
    exact ⟨x,hc⟩

/-- A nonzero factor in one generated residual channel suffices, even for a
nonlinear F and a restricted input domain. The equality excludes cancellation. -/
theorem realized_of_residual_factor (x : X) (z : ℂ) (k : IntertwiningMap a b)
    (hF : ((DipoleSMCoefficient.equiv a b) (F x)).1 = z • k)
    (hz : z ≠ 0) (hk : electron (k mu) ≠ 0) :
    selector a b mu electron (F x) ≠ 0 := by
  intro h
  have he := congrArg Prod.fst h
  change electron (((DipoleSMCoefficient.equiv a b) (F x)).1 mu) = 0 at he
  rw [hF] at he
  simp only [IntertwiningMap.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul] at he
  exact (mul_ne_zero hz hk) he

end
end Physics.DipoleFlavorSelection
