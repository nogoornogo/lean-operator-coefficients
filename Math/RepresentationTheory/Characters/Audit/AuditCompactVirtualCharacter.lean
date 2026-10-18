import Math.RepresentationTheory.Characters.CompactVirtualCharacter
import Math.RepresentationTheory.Multiplicity.CompactVirtualMultiplicityIndex
import TauCeti.RepresentationTheory.LinearCharacter.Basic
import Mathlib.Analysis.Complex.Circle
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

namespace Math.CompactVirtualCharacterAudit
noncomputable section
open Representation ContinuousRepresentationScope CompactVirtualCharacter

@[simp] theorem trivial_character {L : Type*} [AddCommGroup L] [Module ℂ L]
    [FiniteDimensional ℂ L] (z : Circle) :
    (Representation.trivial ℂ Circle L).character z = (Module.finrank ℂ L : ℂ) := by
  simp [Representation.character, Representation.trivial]

def circleFamily : Fin 2 → Representation ℂ Circle ℂ :=
  ![ofLinearCharacter 1, ofLinearCharacter Circle.toUnits]

instance (i : Fin 2) : IsIrreducible (circleFamily i) := by
  fin_cases i <;> dsimp [circleFamily] <;> infer_instance

theorem circle_continuous (i : Fin 2) : IsJointlyContinuous (circleFamily i) := by
  fin_cases i
  · change Continuous (fun p : Circle × ℂ => (1 : ℂ) * p.2)
    fun_prop
  · change Continuous (fun p : Circle × ℂ => (p.1 : ℂ) * p.2)
    fun_prop

theorem circle_distinct (i j : Fin 2) (h : i ≠ j) :
    IsEmpty (Representation.Equiv (circleFamily i) (circleFamily j)) := by
  constructor
  intro e
  have he := congrFun (char_iso e) (-1 : Circle)
  fin_cases i <;> fin_cases j <;>
    norm_num [circleFamily, char_ofLinearCharacter] at *

def signedCoefficients : Fin 2 → ℤ := ![2, -1]

theorem signed_dimension : dimension (V := fun _ : Fin 2 => ℂ) signedCoefficients = 1 := by
  norm_num [dimension, signedCoefficients, Fin.sum_univ_two]

theorem signed_character (z : Circle) :
    character circleFamily signedCoefficients z = 2 - (z : ℂ) := by
  simp [CompactVirtualCharacter.character, circleFamily, signedCoefficients, Fin.sum_univ_two,
    char_ofLinearCharacter, sub_eq_add_neg]

theorem actual_difference (z : Circle) :
    (Representation.trivial ℂ Circle (Fin 2 → ℂ)).character z -
      (circleFamily 1).character z = character circleFamily signedCoefficients z := by
  rw [signed_character]
  simp [circleFamily, char_ofLinearCharacter]

theorem actual_split : Nonempty (SplitRepresentationProjection.Split
    (Representation.trivial ℂ Circle (Fin 2 → ℂ)) (circleFamily 0)) := by
  let : MeasurableSpace Circle := borel Circle
  let : BorelSpace Circle := ⟨rfl⟩
  apply exists_split circleFamily signedCoefficients circle_continuous circle_distinct
    (Representation.trivial ℂ Circle (Fin 2 → ℂ)) (circleFamily 1)
    (by change Continuous (fun p : Circle × (Fin 2 → ℂ) => p.2); fun_prop)
    (circle_continuous 1) actual_difference 0
  norm_num [signedCoefficients]

theorem negative_coefficient : signedCoefficients 1 < 0 := by decide

theorem not_actual {L : Type*} [NormedAddCommGroup L] [NormedSpace ℂ L]
    [FiniteDimensional ℂ L] (rho : Representation ℂ Circle L)
    (hc : IsJointlyContinuous rho) :
    ¬ (∀ z, rho.character z = character circleFamily signedCoefficients z) := by
  intro he
  let : MeasurableSpace Circle := borel Circle
  let : BorelSpace Circle := ⟨rfl⟩
  have hn := nonnegative_of_actual circleFamily signedCoefficients
    circle_continuous circle_distinct rho hc he 1
  norm_num [signedCoefficients] at hn

theorem zero_dimension : dimension (V := fun _ : Fin 2 => ℂ) ![0, 0] = 0 := by
  norm_num [dimension, Fin.sum_univ_two]

theorem negative_dimension : dimension (V := fun _ : Fin 2 => ℂ) ![1, -2] = -1 := by
  norm_num [dimension, Fin.sum_univ_two]

end
end Math.CompactVirtualCharacterAudit

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod || (`Physics).isPrefixOf mod then
      throwError "Virtual character imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.CompactVirtualCharacterAudit.trivial_character,
    ``Math.CompactVirtualCharacter.character_one,
    ``Math.CompactVirtualCharacter.dimension_pos_of_actual,
    ``Math.CompactVirtualCharacter.exists_positive,
    ``Math.CompactVirtualCharacter.pairing,
    ``Math.CompactVirtualCharacter.character_injective,
    ``Math.CompactVirtualCharacter.nonnegative_of_actual,
    ``Math.CompactVirtualCharacter.hom_difference,
    ``Math.CompactVirtualCharacter.exists_split,
    ``Math.CompactVirtualMultiplicityIndex.exists_split,
    ``Math.CompactVirtualCharacterAudit.circle_continuous,
    ``Math.CompactVirtualCharacterAudit.circle_distinct,
    ``Math.CompactVirtualCharacterAudit.signed_dimension,
    ``Math.CompactVirtualCharacterAudit.signed_character,
    ``Math.CompactVirtualCharacterAudit.actual_difference,
    ``Math.CompactVirtualCharacterAudit.actual_split,
    ``Math.CompactVirtualCharacterAudit.negative_coefficient,
    ``Math.CompactVirtualCharacterAudit.not_actual,
    ``Math.CompactVirtualCharacterAudit.zero_dimension,
    ``Math.CompactVirtualCharacterAudit.negative_dimension]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Virtual character: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Virtual character: {declarations.length} strict axiom checks passed"
