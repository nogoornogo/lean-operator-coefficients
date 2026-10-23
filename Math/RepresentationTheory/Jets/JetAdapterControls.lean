import Math.RepresentationTheory.Relations.FiniteLocalExtraRelations
import Math.RepresentationTheory.Jets.JetInputAdapter
import Math.Algebra.Jets.MixedJetQuadratic

/-! Complete mixed positive-grade control in the same public relation/Hom input. -/
namespace Math.JetAdapterControls
set_option autoImplicit false
noncomputable section
open Representation MixedJetQuadratic

@[reducible] local instance : AddCommGroup Source := inferInstance
@[reducible] local instance : Module ℂ Source := inferInstance

abbrev action : Representation ℂ Unit Source := trivial ℂ Unit Source
abbrev Input := JetInputAdapter.Input action (trivial ℂ Unit ℂ) relations

theorem stable : ∀ h : Unit, relations ≤ relations.comap (action h) := fun _ _ hp => hp

def equiv := JetInputAdapter.equiv action (trivial ℂ Unit ℂ) relations stable

/-- This actual complete mixed source has precisely the single computed IBP relation. -/
theorem admissible_iff (f : IntertwiningMap action (trivial ℂ Unit ℂ)) :
    f ∈ Input ↔ f first + f second = 0 := by
  change relations ≤ f.toLinearMap.ker ↔ _
  rw [relations_span, Submodule.span_singleton_le_iff_mem]
  change f (first + second) = 0 ↔ _
  rw [map_add]

@[simp] theorem extraction (f : Input) (p : Source) :
    equiv f (relations.mkQ p) = f.val p := rfl

/-- Concrete finite-local input with the original single scalar contraction. -/
abbrev scalarLocal : Representation ℂ Unit ℂ := trivial ℂ Unit ℂ

def scalarContraction : IntertwiningMap scalarLocal scalarLocal where
  toLinearMap := LinearMap.id
  isIntertwining' _ := rfl

theorem scalar_probes (i j : Unit) : scalarContraction (1 : ℂ) = if i = j then 1 else 0 := by
  simp [scalarContraction]

theorem scalar_complete (f : IntertwiningMap scalarLocal scalarLocal) :
    f = ∑ _i : Unit, f 1 • scalarContraction := by
  rw [Fintype.sum_unique]
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  change f.toLinearMap z = f.toLinearMap 1 * z
  have h := f.toLinearMap.map_smul z (1 : ℂ)
  simpa only [smul_eq_mul, mul_one, mul_comm] using h


def noLocalExchange : Empty → Representation.Equiv scalarLocal scalarLocal := Empty.elim
def noFlavorExchange : Empty → Representation.Equiv action action := Empty.elim

open scoped TensorProduct

def liftedRelations : Submodule ℂ (ℂ ⊗[ℂ] Source) :=
  relations.map (TensorProduct.lid ℂ Source).symm.toLinearMap

theorem lifted_stable : ∀ h : Unit, liftedRelations ≤ liftedRelations.comap
    (FiniteLocalExtraRelations.sourceAction (A := ℂ) action h) := by
  rintro h _ ⟨u, hu, rfl⟩
  refine ⟨u, hu, ?_⟩
  exact IntertwiningMap.isIntertwining _ _
    (Representation.TensorProduct.lid ℂ action).symm.toIntertwiningMap h u

def finiteEquiv := FiniteLocalExtraRelations.equiv scalarLocal action
  (fun _ : Unit => scalarContraction) (fun _ => (1 : ℂ)) scalar_probes scalar_complete
  noLocalExchange noFlavorExchange Empty.elim liftedRelations lifted_stable

/-- The computed finite-local input really carries the actual mixed IBP relation. -/
theorem finite_admissible_iff (f : FiniteLocalExtraRelations.Coefficient
    scalarLocal action noLocalExchange noFlavorExchange Empty.elim) :
    f ∈ FiniteLocalExtraRelations.Input scalarLocal action noLocalExchange noFlavorExchange
      Empty.elim liftedRelations ↔
    f.val (1 ⊗ₜ[ℂ] first) + f.val (1 ⊗ₜ[ℂ] second) = 0 := by
  change liftedRelations ≤ f.val.toLinearMap.ker ↔ _
  constructor
  · intro h
    have he := h ⟨first + second, by rw [relations_span]; exact Submodule.subset_span (Set.mem_singleton _), rfl⟩
    change f.val (1 ⊗ₜ[ℂ] (first + second)) = 0 at he
    simpa only [TensorProduct.tmul_add, map_add] using he
  · intro h
    rintro _ ⟨u, hu, rfl⟩
    have hl : relations ≤ (f.val.toLinearMap.comp (TensorProduct.lid ℂ Source).symm.toLinearMap).ker := by
      rw [relations_span, Submodule.span_singleton_le_iff_mem]
      change f.val (1 ⊗ₜ[ℂ] (first + second)) = 0
      simpa only [TensorProduct.tmul_add, map_add] using h
    exact hl hu

end
end Math.JetAdapterControls
