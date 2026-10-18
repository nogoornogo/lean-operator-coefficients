import Math.RepresentationTheory.AutomorphismCovariantHom

/-! Gauge removal on coinvariants does not require a homomorphic gauge lift.
The removed field maps need not form a representation. -/
namespace Math.PointwiseGaugeRemoval
set_option autoImplicit false
noncomputable section
open Representation AutomorphismCovariantHom
variable {k G H V : Type*} [Field k] [Group G] [Group H]
  [AddCommGroup V] [Module k V]
  (a : Representation k G V) (alpha : H →* MulAut G) (A : Action a alpha)

abbrev projection := (LocalCoinvariantHom.relations a).mkQ

/-- Every local gauge transformation acts trivially after local coinvariants. -/
theorem projection_local (g : G) (v : V) :
    projection a (a g v) = projection a v := by
  have hm : a g v - v ∈ LocalCoinvariantHom.relations a :=
    Submodule.subset_span ⟨(g, v), rfl⟩
  have hz : projection a (a g v - v) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hm
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

/-- An arbitrary pointwise gauge representative, not a homomorphism. -/
def removed (s : H → G) (h : H) : Module.End k V := a (s h)⁻¹ * A.residual h

/-- Gauge removal changes no induced coefficient-carrier action. -/
theorem removed_projection (s : H → G) (h : H) (v : V) :
    projection a (removed a alpha A s h v) =
      (AutomorphismCovariantHom.quotient a alpha A) h (projection a v) :=
  projection_local a _ _

/-- The pointwise removed maps satisfy the group law after projection, even
when they do not satisfy it on the field carrier. -/
theorem removed_mul_projection (s : H → G) (h l : H) (v : V) :
    projection a (removed a alpha A s h (removed a alpha A s l v)) =
      projection a (removed a alpha A s (h * l) v) := by
  rw [removed_projection, removed_projection, removed_projection]
  simp only [map_mul, Module.End.mul_apply]

/-- A locally invariant functional cannot distinguish physical and removed maps. -/
theorem invariant_removed (s : H → G) (f : V →ₗ[k] k)
    (hf : ∀ g v, f (a g v) = f v) (h : H) (v : V) :
    f (removed a alpha A s h v) = f (A.residual h v) := hf _ _

/-- If the lift actually implements the inner automorphism, every removed map
commutes with the gauge action. This still does not supply its group law. -/
theorem removed_commutes (s : H → G)
    (hs : ∀ h g, alpha h g = s h * g * (s h)⁻¹) (h : H) (g : G) :
    removed a alpha A s h * a g = a g * removed a alpha A s h := by
  have hc : A.residual h * a g = a (alpha h g) * A.residual h := by
    ext v
    exact A.covariance h g v
  unfold removed
  rw [mul_assoc, hc, ← mul_assoc, ← map_mul, hs]
  have hg : (s h)⁻¹ * (s h * g * (s h)⁻¹) = g * (s h)⁻¹ := by
    simp only [← mul_assoc, inv_mul_cancel, one_mul]
  rw [hg, map_mul, mul_assoc]

section Comparison
variable (gamma : H →* MulAut G) (B : Action a gamma)

/-- Two supplied genuine actions differing pointwise by a local gauge factor
have exactly the same induced action on local coinvariants. -/
theorem quotient_eq (s : H → G)
    (hs : ∀ h v, A.residual h v = a (s h) (B.residual h v)) :
    AutomorphismCovariantHom.quotient a alpha A =
      AutomorphismCovariantHom.quotient a gamma B := by
  apply MonoidHom.ext
  intro h
  apply LinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := (LocalCoinvariantHom.relations a).mkQ_surjective v
  change projection a (A.residual h w) = projection a (B.residual h w)
  rw [hs, projection_local]

/-- Transport of invariant coefficients requires an actual reference action,
not merely pointwise commuting projective maps. -/
def invariantEquiv (s : H → G)
    (hs : ∀ h v, A.residual h v = a (s h) (B.residual h v)) :
    LocalCoinvariantHom.invariantHom a A.residual (trivial k H k) ≃ₗ[k]
      LocalCoinvariantHom.invariantHom a B.residual (trivial k H k) :=
  (AutomorphismCovariantHom.equiv a alpha A (trivial k H k)).trans
    (by
      rw [quotient_eq a alpha A gamma B s hs]
      exact (AutomorphismCovariantHom.equiv a gamma B (trivial k H k)).symm)

/-- A forbidden result transfers exactly under the checked gauge comparison. -/
theorem forbidden_iff (s : H → G)
    (hs : ∀ h v, A.residual h v = a (s h) (B.residual h v)) :
    (∀ f : LocalCoinvariantHom.invariantHom a A.residual (trivial k H k), f = 0) ↔
    ∀ f : LocalCoinvariantHom.invariantHom a B.residual (trivial k H k), f = 0 := by
  let e := invariantEquiv a alpha A gamma B s hs
  constructor
  · intro hf q
    obtain ⟨f, rfl⟩ := e.surjective q
    rw [hf f, map_zero]
  · intro hq f
    apply e.injective
    exact (hq (e f)).trans (map_zero e).symm
/-- Nonzero coefficients transfer as well; this asserts no premise of a
particular reference-model nonzero theorem. -/
theorem nonzero_iff (s : H → G)
    (hs : ∀ h v, A.residual h v = a (s h) (B.residual h v)) :
    (∃ f : LocalCoinvariantHom.invariantHom a A.residual (trivial k H k), f ≠ 0) ↔
    ∃ f : LocalCoinvariantHom.invariantHom a B.residual (trivial k H k), f ≠ 0 := by
  classical
  simpa only [not_forall] using
    not_congr (forbidden_iff a alpha A gamma B s hs)
end Comparison

end
end Math.PointwiseGaugeRemoval
