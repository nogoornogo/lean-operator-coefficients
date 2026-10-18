import Math.RepresentationTheory.FiniteInvariantKernel

/-! An exact finite kernel for one group factor, retaining the other factor's conditions. -/
namespace Math.PartialInvariantKernel
set_option autoImplicit false
noncomputable section
open Representation
variable {G K V I J : Type*} [Group G] [Group K] [AddCommGroup V] [Module ℂ V]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  (rho : Representation ℂ (G × K) V) (b : Module.Basis J ℂ V) (tests : I → K)

abbrev tested := rho.comp (MonoidHom.inr G K)

/-- Finite K rows together with the still explicit actual G invariance conditions. -/
def Space : Submodule ℂ (J → ℂ) where
  carrier := {c | c ∈ FiniteInvariantKernel.Kernel (tested rho) b tests ∧
    ∀ g x, (FiniteInvariantKernel.coordinates b).symm c (rho (g,1) x) =
      (FiniteInvariantKernel.coordinates b).symm c x}
  zero_mem' := ⟨Submodule.zero_mem _, by simp⟩
  add_mem' := by
    rintro c d ⟨hc,hg⟩ ⟨hd,hh⟩
    refine ⟨Submodule.add_mem _ hc hd, ?_⟩
    intro g x
    simp [hg g x, hh g x]
  smul_mem' := by
    rintro z c ⟨hc,hg⟩
    refine ⟨Submodule.smul_mem _ z hc, ?_⟩
    intro g x
    simp [hg g x]

def equiv (he : FiniteInvariantKernel.Exhaustive (tested rho) tests) :
    InvariantCoefficientTransport.Invariants rho ≃ₗ[ℂ] Space rho b tests where
  toFun f := ⟨FiniteInvariantKernel.coordinates b f.toLinearMap, by
    refine ⟨(FiniteInvariantKernel.mem_kernel_iff (tested rho) b tests _).mpr ?_, ?_⟩
    · intro i x
      exact f.isIntertwining _ _ (1,tests i) x
    · intro g x
      simp only [LinearEquiv.symm_apply_apply]
      exact f.isIntertwining _ _ (g,1) x⟩
  invFun c :=
    { toLinearMap := (FiniteInvariantKernel.coordinates b).symm c.val
      isIntertwining' gh := by
        apply LinearMap.ext
        intro x
        let f := (FiniteInvariantKernel.coordinates b).symm c.val
        have hk := he f ((FiniteInvariantKernel.mem_kernel_iff (tested rho) b tests f).mp
          (by simpa [f] using c.property.1))
        change f (rho gh x) = f x
        have hm : rho gh x = rho (gh.1,1) (rho (1,gh.2) x) := by
          rw [← Module.End.mul_apply, ← map_mul]
          simp
        rw [hm, c.property.2]
        exact hk gh.2 x }
  left_inv f := IntertwiningMap.ext ((FiniteInvariantKernel.coordinates b).symm_apply_apply _)
  right_inv c := Subtype.ext ((FiniteInvariantKernel.coordinates b).apply_symm_apply _)
  map_add' f h := Subtype.ext ((FiniteInvariantKernel.coordinates b).map_add _ _)
  map_smul' z f := Subtype.ext ((FiniteInvariantKernel.coordinates b).map_smul z _)

omit [Fintype I] [DecidableEq I] in
theorem allowed_iff (he : FiniteInvariantKernel.Exhaustive (tested rho) tests) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants rho) ↔
      SelectionCriteria.Allowed (Space rho b tests) :=
  SelectionCriteria.allowed_equiv (equiv rho b tests he)

end
end Math.PartialInvariantKernel
