import Math.RepresentationTheory.Exterior.ConstantPatternExterior

/-! Action transport through the constant-content statistical equivalence. -/
namespace Math.ConstantExteriorAction
set_option autoImplicit false
noncomputable section
open Representation
variable {S G : Type*} [Fintype S] [DecidableEq S] [Group G]
  {V : S → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  (r : ∀ s, Representation ℂ G (V s)) (s : S) (n : ℕ)

theorem forward_action (g : G) (x : ⋀[ℂ]^n (V s)) :
    PatternExteriorSource.representation r (fun _ : Fin n => s) g
      (ConstantPatternExterior.linearEquiv r s n x) =
    ConstantPatternExterior.linearEquiv r s n ((r s).exteriorPower n g x) :=
  ((ConstantPatternExterior.equiv r s n).isIntertwining _ _ g x).symm
end
end Math.ConstantExteriorAction
