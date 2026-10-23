import Math.RepresentationTheory.SU2.SL2SymmetricSpan
import Math.RepresentationTheory.Exterior.PatternExteriorSource

/-! Symmetric-power spanning for arbitrary species statistical images. -/
namespace Math.SL2StatisticalSpan
set_option autoImplicit false
noncomputable section
open Representation SL2SymmetricEmbeddings
variable {S : Type*} [Fintype S] [DecidableEq S]
  {V : S → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  (r : ∀ s, Representation ℂ Group (V s))

def single (s : S) : IntertwiningMap (r s) (FiniteSpeciesExterior.representation r) where
  toLinearMap := LinearMap.single ℂ V s
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact (FiniteSpeciesExterior.action_single r g s x).symm

theorem pi (h : ∀ s, SL2SymmetricSpan.Spanned (r s)) :
    SL2SymmetricSpan.Spanned (FiniteSpeciesExterior.representation r) := by
  let M := Submodule.span ℂ (SL2SymmetricSpan.generators (FiniteSpeciesExterior.representation r))
  have hs (s : S) (x : V s) : Pi.single s x ∈ M := by
    have hx : x ∈ Submodule.span ℂ (SL2SymmetricSpan.generators (r s)) := by rw [h s]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n,q,v,rfl⟩ := hx
      exact Submodule.subset_span ⟨n,(single r s).comp q,v,rfl⟩
    | zero => simp [M]
    | add x y _ _ hx hy => simpa only [Pi.single_add] using M.add_mem hx hy
    | smul c x _ hx => simpa only [Pi.single_smul] using M.smul_mem c hx
  apply top_unique
  intro x _
  change x ∈ M
  have he : (∑ s, Pi.single s (x s)) = x := LinearMap.sum_single_apply V x
  exact he ▸ M.sum_mem (fun s _ => hs s (x s))

theorem source {n : ℕ} (p : Fin n → S) (h : ∀ s, SL2SymmetricSpan.Spanned (r s)) :
    SL2SymmetricSpan.Spanned (PatternExteriorSource.representation r p) :=
  SL2SymmetricSpan.of_surjective _ _ (PatternExteriorSource.projection r p)
    (fun x => ⟨x.val, PatternExteriorSource.projection_inclusion r p x⟩)
    (SL2SymmetricSpan.exterior _ (pi r h) n)

end
end Math.SL2StatisticalSpan
