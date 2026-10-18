import Math.RepresentationTheory.Decomposition.FiniteBlockHom
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace Math.IrreducibleHomScalar
set_option autoImplicit false
noncomputable section
open Representation
variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W]
  (a : Representation ℂ G V) (b : Representation ℂ G W)
  [IsIrreducible a]

/-- An actual equivalence identifies the Hom with a scalar multiple of its bridge. -/
theorem scalar_bridge (e : Representation.Equiv a b) (f : IntertwiningMap a b) :
    ∃ z : ℂ, f = z • e.toIntertwiningMap := by
  obtain ⟨z,hz⟩ := BlockCentralizer.intertwiningMap_eq_smul_one_of_irreducible a
    (e.symm.toIntertwiningMap.comp f)
  refine ⟨z,?_⟩
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have he := congrArg (fun t : IntertwiningMap a a => e (t x)) hz
  simpa using he

def scalarBridge (e : Representation.Equiv a b) : ℂ →ₗ[ℂ] IntertwiningMap a b :=
  LinearMap.toSpanSingleton ℂ _ e.toIntertwiningMap

theorem scalarBridge_bijective (e : Representation.Equiv a b) :
    Function.Bijective (scalarBridge a b e) := by
  constructor
  · intro z w h
    have hz : z • (1 : IntertwiningMap a a) = w • 1 := by
      apply IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      have hv := congrArg (fun t : IntertwiningMap a b => e.symm (t x)) h
      simpa [scalarBridge] using hv
    apply (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := a)).injective
    simpa [scalarBridge] using hz
  · intro f
    obtain ⟨z,hz⟩ := scalar_bridge a b e f
    exact ⟨z,hz.symm⟩

def equiv (e : Representation.Equiv a b) : ℂ ≃ₗ[ℂ] IntertwiningMap a b :=
  LinearEquiv.ofBijective (scalarBridge a b e) (scalarBridge_bijective a b e)

variable [IsIrreducible b]
omit [FiniteDimensional ℂ V] in
theorem unmatched_zero (h : ¬ Nonempty (Representation.Equiv a b))
    (f : IntertwiningMap a b) : f = 0 := by
  rcases IsIrreducible.bijective_or_eq_zero f with hf | hf
  · exact False.elim (h ⟨f.ofBijective hf⟩)
  · exact hf
end
end Math.IrreducibleHomScalar
