import Math.RepresentationTheory.TensorPermutationStatistics
import TauCeti.RepresentationTheory.Symmetric.Specht.Ideal.Idempotent
import Mathlib.LinearAlgebra.Projection

/-! Normalized mixed Young projectors on arbitrary flavor tensor powers.
This constructs a tableau component, not a complete family decomposition. -/
namespace Math.YoungTensorProjector
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {H F : Type*} [Group H] [AddCommGroup F] [Module ℂ F]
  (a : Representation ℂ H F) {mu : YoungDiagram} (t : TauCeti.YoungTableau mu)

def normalized : MonoidAlgebra ℂ (Equiv.Perm (Fin mu.card)) :=
  MonoidAlgebra.mapAlgHom _ (Algebra.ofId ℚ ℂ)
    (((Module.finrank ℚ (TauCeti.YoungTableau.spechtIdeal t) : ℚ) /
      (mu.card.factorial : ℚ)) • TauCeti.YoungTableau.youngSymmetrizer t)

theorem normalized_idempotent : IsIdempotentElem (normalized t) :=
  (TauCeti.YoungTableau.isIdempotentElem_smul_youngSymmetrizer t).map
    (MonoidAlgebra.mapAlgHom _ (Algebra.ofId ℚ ℂ))

def projector : IntertwiningMap (a.tensorPower mu.card) (a.tensorPower mu.card) where
  toLinearMap := (TensorPermutationStatistics.permutation (F := F) mu.card).asAlgebraHom (normalized t)
  isIntertwining' h := by
    apply LinearMap.ext
    intro u
    exact congrArg (fun f : Module.End ℂ (⨂[ℂ]^mu.card F) => f u)
      (PiTensorProduct.commute_reindexRepresentation_asAlgebraHom_map
        ℂ F (Fin mu.card) (normalized t) (a h)).eq

theorem projector_idempotent : IsIdempotentElem (projector a t).toLinearMap :=
  (normalized_idempotent t).map
    (TensorPermutationStatistics.permutation (F := F) mu.card).asAlgebraHom

theorem projector_twice (u : ⨂[ℂ]^mu.card F) :
    projector a t (projector a t u) = projector a t u :=
  congrArg (fun f : Module.End ℂ (⨂[ℂ]^mu.card F) => f u) (projector_idempotent a t).eq

theorem range_stable : ∀ h, LinearMap.range (projector a t).toLinearMap ≤
    (LinearMap.range (projector a t).toLinearMap).comap (a.tensorPower mu.card h) := by
  intro h u hu
  obtain ⟨v, rfl⟩ := hu
  exact ⟨a.tensorPower mu.card h v, IntertwiningMap.isIntertwining _ _ (projector a t) h v⟩

theorem kernel_stable : ∀ h, LinearMap.ker (projector a t).toLinearMap ≤
    (LinearMap.ker (projector a t).toLinearMap).comap (a.tensorPower mu.card h) := by
  intro h u hu
  change projector a t (a.tensorPower mu.card h u) = 0
  rw [IntertwiningMap.isIntertwining _ _ (projector a t) h u]
  change projector a t u = 0 at hu
  rw [hu, map_zero]

abbrev component := (a.tensorPower mu.card).subrepresentation
  (LinearMap.range (projector a t).toLinearMap) (range_stable a t)

abbrev quotient := (a.tensorPower mu.card).quotient
  (LinearMap.ker (projector a t).toLinearMap) (kernel_stable a t)

/-- The independently specified projector kernel quotient is the Young image. -/
def quotientEquiv : Representation.Equiv (quotient a t) (component a t) where
  toLinearEquiv := (projector a t).toLinearMap.quotKerEquivRange
  isIntertwining' h := by
    apply LinearMap.ext
    intro u
    obtain ⟨v, rfl⟩ := (LinearMap.ker (projector a t).toLinearMap).mkQ_surjective u
    apply Subtype.ext
    exact IntertwiningMap.isIntertwining _ _ (projector a t) h v

theorem kernel_eq_relations : LinearMap.ker (projector a t).toLinearMap =
    LinearMap.range (LinearMap.id - (projector a t).toLinearMap) :=
  LinearMap.IsIdempotentElem.ker_eq_range (projector_idempotent a t)

theorem range_kernel_complement : IsCompl (LinearMap.range (projector a t).toLinearMap)
    (LinearMap.ker (projector a t).toLinearMap) :=
  LinearMap.IsIdempotentElem.isCompl (projector_idempotent a t)

end
end Math.YoungTensorProjector
