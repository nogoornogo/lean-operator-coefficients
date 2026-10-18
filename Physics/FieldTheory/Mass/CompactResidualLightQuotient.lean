import Physics.FieldTheory.Mass.ResidualMassIndex
import Math.RepresentationTheory.Characters.CompactPositiveCharacterQuotient
import Math.RepresentationTheory.Characters.ResidualWeightContinuity
import Math.RepresentationTheory.Decomposition.CompactIrreducibleQuotient
import Math.RepresentationTheory.Unitary.ContinuousDual

open Math

/-! Positive residual indices on actual light spaces for compact continuous H.
The dual and the split projections live on the original algebraic carriers. -/

namespace GUT.CompactResidualLightQuotient
noncomputable section

open Representation ResidualWeightSpace ResidualWeightCharacter
open SplitRepresentationProjection ContinuousRepresentationScope

variable {T H V P R : Type*} [CommGroup T] [Group H]
  [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
  [NormedAddCommGroup R] [NormedSpace ℂ R] [FiniteDimensional ℂ R]

theorem exists_split_of_index_eq (light : Representation ℂ (T × H) V)
    (hl : IsJointlyContinuous (residual light))
    (chi : T →* Circle) (target : Representation ℂ H P)
    (hp : IsJointlyContinuous target)
    (tau : Representation ℂ H R) [IsIrreducible tau]
    (hr : IsJointlyContinuous tau)
    (ht : ∀ h, index light chi h = target.character h)
    (f : IntertwiningMap target tau) (hf : f ≠ 0) :
    Nonempty (Split (representation light chi) tau) := by
  let := ContinuousDual.dualNormedAddCommGroup (V := space light chi⁻¹)
  let := ContinuousDual.dualNormedSpace (V := space light chi⁻¹)
  have hc : ∀ h, (representation light chi).character h =
      (representation light chi⁻¹).dual.character h + target.character h := by
    intro h
    have he := ht h
    unfold index at he
    linear_combination he
  have hw := ResidualWeightContinuity.weight light hl chi
  have hd := ContinuousDual.jointlyContinuous_dual (representation light chi⁻¹)
    (ResidualWeightContinuity.weight light hl chi⁻¹)
  obtain ⟨p, hsurj⟩ :=
    CompactPositiveCharacterQuotient.exists_surjective_of_character_add_of_nonzero
      (representation light chi) (representation light chi⁻¹).dual target tau
      hw hd hp hr hc f hf
  obtain ⟨S, _⟩ := SemisimpleSplitting.exists_split _ _
    (CompactIrreducibleQuotient.semisimple _ hw) p hsurj
  exact ⟨S⟩

theorem exists_common_quotient (light : Representation ℂ (T × H) V)
    (hl : IsJointlyContinuous (residual light))
    (target : Representation ℂ H P) (hp : IsJointlyContinuous target) [Nontrivial P] :
    ∃ S : Subrepresentation target, IsIrreducible S.toRepresentation ∧
      Nontrivial S.toSubmodule ∧ ∀ chi : T →* Circle,
        (∀ h, index light chi h = target.character h) →
          Nonempty (Split (representation light chi) S.toRepresentation) := by
  obtain ⟨S, hi, hn, f, hf⟩ :=
    CompactIrreducibleQuotient.exists_irreducible_quotient target hp
  let : IsIrreducible S.toRepresentation := hi
  let : Nontrivial S.toSubmodule := hn
  have hfn : f ≠ 0 := by
    intro he
    obtain ⟨x, hx⟩ := exists_ne (0 : S.toSubmodule)
    obtain ⟨y, hy⟩ := hf x
    apply hx
    simpa [he] using hy.symm
  exact ⟨S, hi, hn, fun chi ht => exists_split_of_index_eq light hl chi target hp
    S.toRepresentation (hp.subrepresentation S) ht f hfn⟩

end
end GUT.CompactResidualLightQuotient
