import Math.RepresentationTheory.Content.PatternSpeciesEquiv
import Math.RepresentationTheory.Relations.StatisticalSourceRestriction

/-! Species transport between restrictions of statistical sources. The group
and field representations stay abstract during operator transport. -/
namespace Math.PatternSpeciesRestriction
set_option autoImplicit false
noncomputable section
open Representation
variable {S T G H K : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
  [Group G] [Group H] [Group K]
  {V : S → Type*} {W : T → Type*}
  [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  [∀ t, AddCommGroup (W t)] [∀ t, Module ℂ (W t)]
  (r : ∀ s, Representation ℂ G (V s)) (a : ∀ t, Representation ℂ H (W t))
  (e : S ≃ T) (j : K →* G) (k : K →* H)
  (h : ∀ s, Representation.Equiv ((r s).comp j) ((a (e s)).comp k))
  {n : ℕ} (p : Fin n → S)

def equiv : Representation.Equiv ((PatternExteriorSource.representation r p).comp j)
    ((PatternExteriorSource.representation a (e ∘ p)).comp k) where
  toLinearEquiv := (PatternSpeciesEquiv.equiv (fun s => (r s).comp j)
    (fun t => (a t).comp k) e h p).toLinearEquiv
  isIntertwining' g := by
    have hl := congrArg (fun rho => rho g) (StatisticalSourceRestriction.source
      r j (fun s => (r s).comp j) p (fun _ => rfl))
    have hr := congrArg (fun rho => rho g) (StatisticalSourceRestriction.source
      a k (fun t => (a t).comp k) (e ∘ p) (fun _ => rfl))
    rw [hl,hr]
    exact (PatternSpeciesEquiv.equiv (fun s => (r s).comp j)
      (fun t => (a t).comp k) e h p).isIntertwining' g

end
end Math.PatternSpeciesRestriction
