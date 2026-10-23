import Math.RepresentationTheory.Relations.SignedRelationQuotient
import Mathlib.Tactic.Module

/-! Two-slot Young projectors and signed input quotients for an equivariant
involution. Arbitrary residual group and arbitrary-dimensional carrier. -/
namespace Math.InvolutionYoung
set_option autoImplicit false
noncomputable section
open Representation
variable {H U : Type*} [Group H] [AddCommGroup U] [Module ℂ U]
  (rho : Representation ℂ H U) (t : IntertwiningMap rho rho)
  (ht : ∀ u, t (t u) = u) (s : ℂ) (hs : s * s = 1)

def eigen : Submodule ℂ U := LinearMap.ker (t.toLinearMap - s • LinearMap.id)

theorem mem_eigen (u : U) : u ∈ eigen rho t s ↔ t u = s • u := by
  change t u - s • u = 0 ↔ _
  exact sub_eq_zero

def projector : IntertwiningMap rho rho :=
  (1 / 2 : ℂ) • (IntertwiningMap.id rho + s • t)

theorem projector_apply (u : U) :
    projector rho t s u = (1 / 2 : ℂ) • (u + s • t u) := rfl

include ht hs in
theorem projector_eigen (u : U) : projector rho t s u ∈ eigen rho t s := by
  rw [mem_eigen, projector_apply]
  simp only [map_smul, map_add, ht]
  have hs2 : s ^ 2 = 1 := by simpa [pow_two] using hs
  match_scalars <;> ring_nf
  all_goals simp [hs2]

include hs in
theorem projector_fixed (u : U) (hu : u ∈ eigen rho t s) :
    projector rho t s u = u := by
  rw [mem_eigen] at hu
  rw [projector_apply, hu, smul_smul, hs, one_smul]
  module

theorem eigen_stable : ∀ g, eigen rho t s ≤ (eigen rho t s).comap (rho g) := by
  intro g u hu
  change rho g u ∈ eigen rho t s
  rw [mem_eigen] at hu ⊢
  rw [IntertwiningMap.isIntertwining rho rho t g u, hu, map_smul]

abbrev eigenRepresentation := rho.subrepresentation (eigen rho t s) (eigen_stable rho t s)

abbrev relations := SignedRelationQuotient.relations rho (fun _ : Unit => t) (fun _ => s)

include ht hs in
theorem projector_vanish : relations rho t s ≤ LinearMap.ker (projector rho t s).toLinearMap := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨j, u⟩, rfl⟩
  change projector rho t s (t u - s • u) = 0
  rw [projector_apply]
  simp only [map_sub, map_smul, ht]
  have hs2 : s ^ 2 = 1 := by simpa [pow_two] using hs
  match_scalars <;> ring_nf
  all_goals simp [hs2]
  all_goals norm_num

def project : IntertwiningMap rho (eigenRepresentation rho t s) where
  toLinearMap := (projector rho t s).toLinearMap.codRestrict (eigen rho t s)
    (projector_eigen rho t ht s hs)
  isIntertwining' g := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    exact IntertwiningMap.isIntertwining _ _ (projector rho t s) g u

def descend : IntertwiningMap
    (SignedRelationQuotient.quotientRepresentation rho (fun _ : Unit => t) (fun _ => s))
    (eigenRepresentation rho t s) :=
  RelationQuotient.descend rho (eigenRepresentation rho t s) (relations rho t s)
    (SignedRelationQuotient.stable rho (fun _ : Unit => t) (fun _ => s))
    ⟨project rho t ht s hs, by
      intro u hu
      apply Subtype.ext
      exact projector_vanish rho t ht s hs hu⟩

include hs in
theorem mk_projector (u : U) :
    (relations rho t s).mkQ (projector rho t s u) = (relations rho t s).mkQ u := by
  have hr : t u - s • u ∈ relations rho t s := Submodule.subset_span ⟨((), u), rfl⟩
  have hd : projector rho t s u - u = (s / 2) • (t u - s • u) := by
    rw [projector_apply]
    have hs2 : s ^ 2 = 1 := by simpa [pow_two] using hs
    match_scalars <;> ring_nf
    all_goals simp [hs2]
  apply sub_eq_zero.mp
  rw [← map_sub, hd]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ((relations rho t s).smul_mem _ hr)

def quotientEquiv : Representation.Equiv
    (SignedRelationQuotient.quotientRepresentation rho (fun _ : Unit => t) (fun _ => s))
    (eigenRepresentation rho t s) where
  toLinearEquiv :=
    { toLinearMap := (descend rho t ht s hs).toLinearMap
      invFun := fun u => (relations rho t s).mkQ u.val
      left_inv := by
        intro q
        obtain ⟨u, rfl⟩ := (relations rho t s).mkQ_surjective q
        exact mk_projector rho t s hs u
      right_inv := by
        intro u
        apply Subtype.ext
        exact projector_fixed rho t s hs u.val u.property }
  isIntertwining' := (descend rho t ht s hs).isIntertwining'

include ht hs in
theorem projector_idempotent (u : U) :
    projector rho t s (projector rho t s u) = projector rho t s u :=
  projector_fixed rho t s hs _ (projector_eigen rho t ht s hs u)

theorem projector_sum (u : U) :
    projector rho t 1 u + projector rho t (-1) u = u := by
  simp only [projector_apply]
  module

theorem projector_on_sum
    (u : eigen rho t 1) (v : eigen rho t (-1)) :
    projector rho t 1 (u.val + v.val) = u.val ∧
    projector rho t (-1) (u.val + v.val) = v.val := by
  have hu := (mem_eigen rho t 1 u.val).mp u.property
  have hv := (mem_eigen rho t (-1) v.val).mp v.property
  simp only [one_smul] at hu
  simp only [neg_one_smul] at hv
  simp only [projector_apply, map_add, hu, hv]
  constructor <;> module

/-- The two S2 Young components form the whole carrier, equivariantly. -/
def splitting : Representation.Equiv rho
    ((eigenRepresentation rho t 1).prod (eigenRepresentation rho t (-1))) where
  toLinearEquiv :=
    { toLinearMap := ((project rho t ht 1 (by norm_num)).prod
        (project rho t ht (-1) (by norm_num))).toLinearMap
      invFun := fun uv => uv.1.val + uv.2.val
      left_inv := projector_sum rho t
      right_inv := by
        intro uv
        apply Prod.ext
        · apply Subtype.ext
          exact (projector_on_sum rho t uv.1 uv.2).1
        · apply Subtype.ext
          exact (projector_on_sum rho t uv.1 uv.2).2 }
  isIntertwining' := ((project rho t ht 1 (by norm_num)).prod
    (project rho t ht (-1) (by norm_num))).isIntertwining'

@[simp] theorem quotientEquiv_mk (u : U) :
    (quotientEquiv rho t ht s hs ((relations rho t s).mkQ u)).val =
      projector rho t s u := rfl

@[simp] theorem quotientEquiv_symm (u : eigen rho t s) :
    (quotientEquiv rho t ht s hs).symm u = (relations rho t s).mkQ u.val := rfl

/-- Statistics coefficients are Hom from the actual signed Young component. -/
def coefficientEquiv : StatisticalCompleteness.sector
    (SignedRelationQuotient.action rho (Representation.trivial ℂ H ℂ)
      (fun _ : Unit => t)) (fun _ => s) ≃ₗ[ℂ]
    IntertwiningMap (eigenRepresentation rho t s) (Representation.trivial ℂ H ℂ) :=
  (SignedRelationQuotient.equiv rho (Representation.trivial ℂ H ℂ)
    (fun _ : Unit => t) (fun _ => s)).trans
    (InvariantCoefficientTransport.alongEquiv (quotientEquiv rho t ht s hs))

end
end Math.InvolutionYoung
