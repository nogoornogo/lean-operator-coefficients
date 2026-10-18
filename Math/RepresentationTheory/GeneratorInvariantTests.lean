import Math.RepresentationTheory.FiniteInvariantKernel

/-! Actual group generation certifies invariant-functional tests. -/
namespace Math.GeneratorInvariantTests
set_option autoImplicit false
noncomputable section
open Representation
variable {G V T : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  (rho : Representation ℂ G V)

def fixing (f : Module.Dual ℂ V) : Subgroup G where
  carrier := {g | ∀ x, f (rho g x) = f x}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro g h hg hh x
    rw [map_mul, Module.End.mul_apply, hg, hh]
  inv_mem' := by
    intro g hg x
    have he := hg (rho g⁻¹ x)
    simpa [← Module.End.mul_apply, ← map_mul] using he.symm

theorem invariant_iff (generators : T → G)
    (hg : Subgroup.closure (Set.range generators) = ⊤) (f : Module.Dual ℂ V) :
    (∀ g x, f (rho g x) = f x) ↔ ∀ t x, f (rho (generators t) x) = f x := by
  constructor
  · intro hf t; exact hf (generators t)
  · intro hf
    have he : Subgroup.closure (Set.range generators) ≤ fixing rho f := by
      apply (Subgroup.closure_le (fixing rho f)).mpr
      rintro _ ⟨t,rfl⟩
      exact hf t
    rw [hg] at he
    intro g
    exact he (Subgroup.mem_top g)

theorem exhaustive {I : Type*} [Fintype I] [DecidableEq I] (tests : I → G)
    (hg : Subgroup.closure (Set.range tests) = ⊤) : FiniteInvariantKernel.Exhaustive rho tests := by
  intro f hf
  exact (invariant_iff rho tests hg f).mpr hf

end
end Math.GeneratorInvariantTests
