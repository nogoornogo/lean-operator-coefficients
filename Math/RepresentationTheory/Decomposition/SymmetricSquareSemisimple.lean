import Math.RepresentationTheory.Tensors.TensorSquareMultilinear
import Math.RepresentationTheory.Decomposition.CompactIrreducibleQuotient
import Math.RepresentationTheory.Unitary.ContinuousConstructions

/-! Semisimplicity of the symmetric square, without choosing a topology on
the quotient. Compact continuity is used only to unitarize the original action. -/
namespace Math.SymmetricSquareSemisimple
noncomputable section
open Representation ContinuousRepresentationScope
open scoped TensorProduct MonoidAlgebra

variable {H A : Type*} [Group H] [AddCommGroup A] [Module ℂ A]
  (a : Representation ℂ H A)

def quotient : IntertwiningMap (a.tprod a) (a.symmetricPower 2) where
  toLinearMap := TensorSquareMultilinear.fromMultilinear (SymmetricPower.tprod ℂ)
  isIntertwining' h := by
    apply TensorProduct.ext'
    intro x y
    change SymmetricPower.tprod ℂ ![a h x, a h y] =
      (a.symmetricPower 2) h (SymmetricPower.tprod ℂ ![x, y])
    rw [Representation.symmetricPower_apply_tprod]
    congr 1
    ext i
    fin_cases i <;> rfl

theorem quotient_surjective : Function.Surjective (quotient a) := by
  change Function.Surjective (quotient a).toLinearMap
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← SymmetricPower.span_tprod_eq_top ℂ (Fin 2) A]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, rfl⟩
  refine ⟨v 0 ⊗ₜ[ℂ] v 1, ?_⟩
  change SymmetricPower.tprod ℂ ![v 0, v 1] = SymmetricPower.tprod ℂ v
  congr 1
  ext i
  fin_cases i <;> rfl

theorem of_tensor (ht : IsSemisimpleRepresentation (a.tprod a)) :
    IsSemisimpleRepresentation (a.symmetricPower 2) := by
  let : IsSemisimpleModule ℂ[H] (a.tprod a).asModule :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp ht
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  exact IsSemisimpleModule.of_surjective
    (IntertwiningMap.equivLinearMapAsModule _ _ (quotient a)) (quotient_surjective a)

end

noncomputable section
open Representation ContinuousRepresentationScope
variable {H A : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [NormedAddCommGroup A] [NormedSpace ℂ A] [FiniteDimensional ℂ A]
  (a : Representation ℂ H A)

theorem of_compact (ha : IsJointlyContinuous a) :
    IsSemisimpleRepresentation (a.symmetricPower 2) := by
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let b := Module.finBasis ℂ A
  have hc : ∀ i j, Continuous fun h => b.coord i (a h (b j)) := fun i j =>
    (b.coord i).continuous_of_finiteDimensional.comp (ha.orbit (b j))
  let m := (FiniteBasisUnitaryModel.model b a hc).toRepresentation
  let e := FiniteBasisUnitaryModel.modelEquiv b a hc
  have hm := FiniteBasisUnitaryModel.model_inner b a hc
  have ht := UnitaryMultiplicity.isSemisimpleRepresentation_of_unitary (m.tprod m)
    (ContinuousUnitaryConstructions.unitary_tprod m m hm hm)
  have hs := of_tensor m ht
  let es := e.symmetricPower 2
  let f := IntertwiningMap.equivLinearMapAsModule _ _ es.toIntertwiningMap
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule] at hs ⊢
  exact (f.isSemisimpleModule_iff_of_bijective es.bijective).mpr hs

end
end Math.SymmetricSquareSemisimple
