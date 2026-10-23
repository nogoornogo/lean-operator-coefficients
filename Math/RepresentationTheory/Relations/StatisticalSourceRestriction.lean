import Math.RepresentationTheory.Exterior.PatternExteriorSource

/-! Restriction identities without unfolding concrete statistical carriers. -/
namespace Math.StatisticalSourceRestriction
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {S G K : Type*} [Fintype S] [DecidableEq S] [Group G] [Group K]
  {V : S → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  (r : ∀ s, Representation ℂ G (V s)) (j : K →* G)
  (a : ∀ s, Representation ℂ K (V s))

theorem source {n : ℕ} (p : Fin n → S) (h : ∀ s, (r s).comp j = a s) :
    (PatternExteriorSource.representation r p).comp j = PatternExteriorSource.representation a p := by
  ext g : 1
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change exteriorPower.map n ((FiniteSpeciesExterior.representation r) (j g)) x.val =
    exteriorPower.map n ((FiniteSpeciesExterior.representation a) g) x.val
  have he : (FiniteSpeciesExterior.representation r) (j g) =
      (FiniteSpeciesExterior.representation a) g := by
    apply LinearMap.ext
    intro v
    funext s
    exact LinearMap.congr_fun (congrArg (fun rho => rho g) (h s)) (v s)
  rw [he]

theorem tensor {U W : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
    (rho : Representation ℂ G U) (sigma : Representation ℂ G W)
    (a : Representation ℂ K U) (b : Representation ℂ K W)
    (hr : rho.comp j = a) (hs : sigma.comp j = b) : (rho.tprod sigma).comp j = a.tprod b := by
  ext g : 1
  apply TensorProduct.ext'
  intro x y
  change rho (j g) x ⊗ₜ[ℂ] sigma (j g) y = a g x ⊗ₜ[ℂ] b g y
  exact congrArg₂ (fun u v => u ⊗ₜ[ℂ] v)
    (LinearMap.congr_fun (congrArg (fun r => r g) hr) x)
    (LinearMap.congr_fun (congrArg (fun r => r g) hs) y)

end
end Math.StatisticalSourceRestriction
