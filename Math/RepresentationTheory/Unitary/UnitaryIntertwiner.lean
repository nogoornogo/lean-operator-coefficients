import Math.RepresentationTheory.Multiplicity.UnitaryMultiplicity
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Isometric replacement of unitary intertwiners

An algebraic equivalence between finite-dimensional unitary representations
can be replaced by an isometric one. The positive square root of its Gram
operator commutes with the source action, so polar normalization preserves
equivariance. No topology or compactness on the acting group is required.
-/

namespace Math.UnitaryIntertwiner

noncomputable section

open ContinuousLinearMap

variable {G E F : Type*} [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

variable {rho : Representation ℂ G E} {sigma : Representation ℂ G F}

/-- Taking adjoints reverses a unitary intertwiner. -/
theorem adjoint_intertwines
    (hr : UnitaryMultiplicity.IsUnitaryRepresentation rho)
    (hs : UnitaryMultiplicity.IsUnitaryRepresentation sigma)
    (f : E →L[ℂ] F) (hf : ∀ g x, f (rho g x) = sigma g (f x))
    (g : G) (y : F) : f.adjoint (sigma g y) = rho g (f.adjoint y) := by
  apply ext_inner_left ℂ
  intro x
  calc
    inner ℂ x (f.adjoint (sigma g y)) = inner ℂ (f x) (sigma g y) :=
      f.adjoint_inner_right x _
    _ = inner ℂ (f (rho g⁻¹ x)) y := by
      rw [hf]
      simpa using hs g (sigma g⁻¹ (f x)) y
    _ = inner ℂ (rho g⁻¹ x) (f.adjoint y) := (f.adjoint_inner_right _ _).symm
    _ = inner ℂ x (rho g (f.adjoint y)) := by
      simpa using (hr g (rho g⁻¹ x) (f.adjoint y)).symm

/-- An algebraic equivalence of unitary representations admits an isometric replacement. -/
theorem exists_isometric_intertwiner
    (hr : UnitaryMultiplicity.IsUnitaryRepresentation rho)
    (hs : UnitaryMultiplicity.IsUnitaryRepresentation sigma)
    (e : E ≃ₗ[ℂ] F) (he : ∀ g x, e (rho g x) = sigma g (e x)) :
    ∃ u : E ≃ₗᵢ[ℂ] F, ∀ g x, u (rho g x) = sigma g (u x) := by
  let f : E →L[ℂ] F := e.toLinearMap.toContinuousLinearMap
  let A : E →L[ℂ] E := f.adjoint.comp f
  have hA : 0 ≤ A := by
    rw [nonneg_iff_isPositive]
    exact isPositive_adjoint_comp_self f
  let S : E →L[ℂ] E := CFC.sqrt A
  have hS : S * S = A := CFC.sqrt_mul_sqrt_self A hA
  have hSstar : S.adjoint = S := (CFC.sqrt_nonneg A).star_eq
  have hAi : Function.Injective A :=
    f.adjoint_comp_self_injective_iff.mpr e.injective
  have hSi : Function.Injective S := by
    intro x y hxy
    apply hAi
    have hxy' : (S * S) x = (S * S) y := congrArg S hxy
    rwa [hS] at hxy'
  let s : E ≃ₗ[ℂ] E := LinearEquiv.ofBijective S.toLinearMap
    ⟨hSi, (LinearMap.injective_iff_surjective).mp hSi⟩
  have hinner (x y : E) : inner ℂ (f x) (f y) = inner ℂ (s x) (s y) := by
    calc
      inner ℂ (f x) (f y) = inner ℂ x (A y) := (f.adjoint_inner_right x (f y)).symm
      _ = inner ℂ x (S (S y)) := by rw [← hS]; rfl
      _ = inner ℂ (s x) (s y) := by
        change inner ℂ x (S (S y)) = inner ℂ (S x) (S y)
        simpa only [hSstar] using S.adjoint_inner_right x (S y)
  let u : E ≃ₗᵢ[ℂ] F :=
    { s.symm.trans e with
      norm_map' := (LinearMap.norm_map_iff_inner_map_map _).mpr (by
        intro x y
        simpa [f] using hinner (s.symm x) (s.symm y)) }
  refine ⟨u, ?_⟩
  have hAcomm (g : G) : Commute A (rho g).toContinuousLinearMap := by
    ext x
    exact (congrArg f.adjoint (he g x)).trans (adjoint_intertwines hr hs f he g (f x))
  have hScomm (g : G) : Commute S (rho g).toContinuousLinearMap :=
    (hAcomm g).cfcₙ_nnreal NNReal.sqrt
  intro g x
  change e (s.symm (rho g x)) = sigma g (e (s.symm x))
  rw [← he]
  congr 1
  apply s.injective
  have hc : s (rho g (s.symm x)) = rho g (s (s.symm x)) :=
    congrArg (fun T : E →L[ℂ] E => T (s.symm x)) (hScomm g).eq
  simpa using hc.symm

end

end Math.UnitaryIntertwiner
