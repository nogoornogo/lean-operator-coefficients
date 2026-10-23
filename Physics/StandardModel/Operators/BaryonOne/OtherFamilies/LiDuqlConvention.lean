import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DuqlExteriorCompleteness

/-! Normalized local interpretation of Li D.37 in paper order L,Q,D,U. -/
namespace Physics.LiDuqlConvention
set_option autoImplicit false
noncomputable section
open SMEpsilonTensor

def paperLocal (q d u : Color) (l w : Weak)
    (sL sQ sD sU : WeylSpinor.Space) : ℂ :=
  eps3 q d u * eps2 l w * eps2 sL sQ * eps2 sD sU

/-- L,Q,D,U to D,U,Q,L is odd. The weak and left bracket reversals
cancel each other; the remaining Fermi minus is explicit. -/
theorem fermionic_reorder (q d u : Color) (l w : Weak)
    (sL sQ sD sU : WeylSpinor.Space) :
    -paperLocal q d u l w sL sQ sD sU =
    -(eps3 d u q * eps2 w l * eps2 sD sU * eps2 sQ sL) := by
  simp [paperLocal, eps3, eps2]; ring

theorem reorder_parity :
    Equiv.Perm.sign (Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3 * Equiv.swap 2 3) = -1 := by
  decide +kernel
end
end Physics.LiDuqlConvention
