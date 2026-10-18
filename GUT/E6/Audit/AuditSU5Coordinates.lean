import GUT.E6.Minuscule.SU5ModelComparison
import Lean.Util.CollectAxioms

open Math

/-!
# Audit of the bounded E6/SU(5) coordinate comparison

No supplied intertwiner, group integration, or E6 global-form identification
enters these results. Integer certificates are checked by the Lean kernel.
-/

set_option autoImplicit false

namespace GUT.E6.Audit

open Math.E6
open Minuscule Minuscule.SU5Coordinates
open scoped Matrix

example (k : Fin 3) (i : Fin 4) (v : Fin 27 → ℂ) :
    actualModelEquiv (complexGenerator k i *ᵥ v) =
      modelInfinitesimal ((fundamentalGenerator k i).map (Int.castRingHom ℂ))
        (actualModelEquiv v) := actual_generator_comparison k i v

example (i : Fin 4) (v : Fin 27 → ℂ) :
    actualModelEquiv (compactY (node i) *ᵥ v) =
      (Complex.I • (modelGenerator 0 i + modelGenerator 1 i)) (actualModelEquiv v) :=
  actual_compactY_comparison i v

-- Omitting the dual-basis sign gives a genuinely wrong matrix entry.
example :
    integralGenerator 0 0
      (coordinate (.inr (.inr (.inl (0, 1)))))
      (coordinate (.inr (.inr (.inl (0, 0))))) = 1 ∧
    blockMatrix (fundamentalGenerator 0 0)
      (.inr (.inr (.inl (0, 1)))) (.inr (.inr (.inl (0, 0)))) = -1 := by
  decide +kernel

-- Both repeated dual blocks are retained, in different D5 grading sectors.
example :
    grade (coordinate (.inr (.inr (.inl (0, 0))))) = 1 ∧
    grade (coordinate (.inr (.inr (.inl (1, 0))))) = -2 := by
  decide +kernel

end GUT.E6.Audit

run_cmd do
  let declarations := [
    ``GUT.E6.Minuscule.SU5Coordinates.coordinate_bijective,
    ``GUT.E6.Minuscule.SU5Coordinates.sign_sq,
    ``GUT.E6.Minuscule.SU5Coordinates.coordinate_grade,
    ``GUT.E6.Minuscule.SU5Coordinates.wedgeMatrix_map,
    ``GUT.E6.Minuscule.SU5Coordinates.blockMatrix_map,
    ``GUT.E6.Minuscule.SU5Coordinates.integral_generator_comparison,
    ``GUT.E6.Minuscule.SU5Coordinates.signedCoordinates,
    ``GUT.E6.Minuscule.SU5Coordinates.signedCoordinates_hermitian,
    ``GUT.E6.Minuscule.SU5Coordinates.complex_generator_comparison,
    ``GUT.E6.Minuscule.SU5Coordinates.generator_intertwining,
    ``GUT.E6.Minuscule.SU5Coordinates.pairSetEquiv,
    ``GUT.E6.Minuscule.SU5Coordinates.exteriorBasis,
    ``GUT.E6.Minuscule.SU5Coordinates.exteriorMatrix_minor,
    ``GUT.E6.Minuscule.SU5Coordinates.exteriorMatrix_one,
    ``GUT.E6.Minuscule.SU5Coordinates.exteriorInfinitesimal_matrix,
    ``GUT.E6.Minuscule.SU5Coordinates.exteriorMatrix_firstOrder,
    ``GUT.E6.Minuscule.SU5Coordinates.dualInfinitesimal_matrix,
    ``GUT.E6.Minuscule.SU5Coordinates.dualInfinitesimal_pairing,
    ``GUT.E6.Minuscule.SU5Coordinates.matter_ten_matrix,
    ``GUT.E6.Minuscule.SU5Coordinates.matter_barFive_matrix,
    ``GUT.E6.Minuscule.SU5Coordinates.exteriorInfinitesimal_leibniz,
    ``GUT.E6.Minuscule.SU5Coordinates.modelCoordinates,
    ``GUT.E6.Minuscule.SU5Coordinates.modelInfinitesimal_coordinates,
    ``GUT.E6.Minuscule.SU5Coordinates.actualModelEquiv,
    ``GUT.E6.Minuscule.SU5Coordinates.actual_generator_comparison,
    ``GUT.E6.Minuscule.SU5Coordinates.actualModelEquiv_hermitian,
    ``GUT.E6.Minuscule.SU5Coordinates.actual_compactX_comparison,
    ``GUT.E6.Minuscule.SU5Coordinates.actual_compactY_comparison,
    ``GUT.E6.Minuscule.SU5Coordinates.actual_compactH_comparison]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6-SU5 coordinates: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6-SU5 coordinates: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6-SU5 coordinates: checked {declarations.length} declarations"
