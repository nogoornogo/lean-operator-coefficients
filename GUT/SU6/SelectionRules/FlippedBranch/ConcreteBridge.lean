import GUT.SU6.SelectionRules.FlippedBranch.Flipped
import GUT.SU6.Characters.WeylMatrix

/-!
# Connecting the concrete Weyl matrix to the flipped coordinate model

`GUT.WeylMatrix` proves a concrete SU(6) signed permutation matrix acts on
diagonal matrices by the `(3 6)` coordinate swap.  This file repackages the six
diagonal entries as the `Flipped.AmbientPoint` coordinates used by the Laurent
polynomial obstruction.
-/

namespace GUT
namespace ConcreteBridge

def ambientPointOfDiag (d : WeylMatrix.I6 -> ℂ) : Flipped.AmbientPoint ℂ :=
  { z1 := d 0
    z2 := d 1
    z3 := d 2
    z4 := d 3
    z5 := d 4
    z6 := d 5 }

theorem ambientPointOfDiag_swap36 (d : WeylMatrix.I6 -> ℂ) :
    ambientPointOfDiag (d ∘ WeylMatrix.swap36) =
      Flipped.AmbientPoint.swap36 (ambientPointOfDiag d) := by
  apply Flipped.AmbientPoint.ext
  · exact congrArg d (by decide : WeylMatrix.swap36 0 = 0)
  · exact congrArg d (by decide : WeylMatrix.swap36 1 = 1)
  · exact congrArg d (by decide : WeylMatrix.swap36 2 = 5)
  · exact congrArg d (by decide : WeylMatrix.swap36 3 = 3)
  · exact congrArg d (by decide : WeylMatrix.swap36 4 = 4)
  · exact congrArg d (by decide : WeylMatrix.swap36 5 = 2)

def conjugatedDiagonalEntries (d : WeylMatrix.I6 -> ℂ) : WeylMatrix.I6 -> ℂ :=
  fun i =>
    (((WeylMatrix.signedSwap36SU : Matrix.specialUnitaryGroup WeylMatrix.I6 ℂ) :
          Matrix WeylMatrix.I6 WeylMatrix.I6 ℂ) *
        Matrix.diagonal d *
        ((WeylMatrix.signedSwap36SU⁻¹ :
            Matrix.specialUnitaryGroup WeylMatrix.I6 ℂ) :
          Matrix WeylMatrix.I6 WeylMatrix.I6 ℂ)) i i

theorem conjugatedDiagonalEntries_eq (d : WeylMatrix.I6 -> ℂ) :
    conjugatedDiagonalEntries d = d ∘ WeylMatrix.swap36 := by
  funext i
  exact WeylMatrix.signedSwap36SU_conj_diagonal_entry d i

theorem concrete_matrix_realizes_swap36WeylActionData (d : WeylMatrix.I6 -> ℂ) :
    ambientPointOfDiag (conjugatedDiagonalEntries d) =
      (Flipped.swap36WeylActionData ℂ).action (ambientPointOfDiag d) := by
  rw [conjugatedDiagonalEntries_eq]
  exact ambientPointOfDiag_swap36 d

end ConcreteBridge
end GUT
