import GUT.SU5.Embeddings.MaximalTorus
import Physics.StandardModel.Spectrum.Representations.TorusCharacter
import Physics.StandardModel.Gauge.Charges.PhysicalTorus

open Physics

open Math

/-! Compare shared physical coordinates with the actual SU(5) embedding. -/

set_option autoImplicit false
open scoped BigOperators
namespace GUT.SU5.PhysicalTorus
open Physics.SU5.PhysicalTorus
open Physics.SU5
open Math.SU5.MaximalTorus
noncomputable section
open MaximalTorus StandardAbelianCharge TorusCharacter

/-- The covering coordinates are the actual standard SM embedding, not a
separately assigned weight convention. -/
theorem hom_gaugePoint (z : Coordinates) :
    StandardModelEmbedding.hom (gaugePoint z) = MaximalTorus.hom (toTorus z) := by
  apply Subtype.ext
  ext i j
  obtain ⟨i, rfl⟩ := StandardModelEmbedding.blockIndexEquiv.surjective i
  obtain ⟨j, rfl⟩ := StandardModelEmbedding.blockIndexEquiv.surjective j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      rw [StandardModelEmbedding.blockIndexEquiv_color,
        StandardModelEmbedding.blockIndexEquiv_color,
        StandardModelEmbedding.hom_color_entry]
      fin_cases i <;> fin_cases j <;>
        norm_num [StandardSMGaugeTensor.phase, gaugePoint, color, diagonalElement,
          MaximalTorus.hom, toTorus, entries, Matrix.diagonal, mul_comm,
          Fin.castAdd, Fin.natAdd, Fin.castLE] <;> rfl
    | inr j =>
      rw [StandardModelEmbedding.blockIndexEquiv_color,
        StandardModelEmbedding.blockIndexEquiv_weak,
        (StandardModelEmbedding.hom_cross_entries (gaugePoint z) i j).1]
      fin_cases i <;> fin_cases j <;>
        norm_num [MaximalTorus.hom, diagonalElement, Matrix.diagonal,
          Fin.castAdd, Fin.natAdd, Fin.castLE]
  | inr i =>
    cases j with
    | inl j =>
      rw [StandardModelEmbedding.blockIndexEquiv_weak,
        StandardModelEmbedding.blockIndexEquiv_color,
        (StandardModelEmbedding.hom_cross_entries (gaugePoint z) j i).2]
      fin_cases i <;> fin_cases j <;>
        norm_num [MaximalTorus.hom, diagonalElement, Matrix.diagonal,
          Fin.castAdd, Fin.natAdd, Fin.castLE]
    | inr j =>
      rw [StandardModelEmbedding.blockIndexEquiv_weak,
        StandardModelEmbedding.blockIndexEquiv_weak,
        StandardModelEmbedding.hom_weak_entry]
      fin_cases i <;> fin_cases j <;>
        norm_num [StandardSMGaugeTensor.phase, gaugePoint, weak, diagonalElement,
          MaximalTorus.hom, toTorus, entries, Matrix.diagonal, mul_comm,
          Fin.castAdd, Fin.natAdd, Fin.castLE] <;> rfl

end

end GUT.SU5.PhysicalTorus
