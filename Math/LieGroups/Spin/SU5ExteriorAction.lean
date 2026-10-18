import Math.LieGroups.Spin.SU5ScalarComparison
import Math.Topology.CompactCharacters

/-! The actual SU(5) lift acts by the ordinary exterior action, with no scalar
twist. Compactness and proved simple connectedness remove the scalar character. -/

set_option autoImplicit false

namespace Math.CompactSpin.ExteriorComparison

noncomputable section

theorem scalar_eq_one (g : SU5) : scalar g = 1 := by
  let := SU5_simplyConnected
  let := SU5_locallyPathConnected
  exact CompactCharacters.complex_eq_one scalarHom scalar_continuous g

theorem actual_eq_exterior (g : SU5) (s : Fock.Space 5) :
    Fock.representation 5 (SU5Inclusion g) s = exteriorAction g s := by
  rw [actual_eq_scalar_exterior, scalar_eq_one, one_smul]

theorem halfSpin_eq_exterior (g : SU5) (s : HalfSpin.Space 5) :
    (HalfSpin.representation 5 (SU5Inclusion g) s : Fock.Space 5) = exteriorAction g s := by
  rw [Fock.halfSpin_restriction, actual_eq_exterior]

theorem actual_fixes_vacuum (g : SU5) :
    Fock.representation 5 (SU5Inclusion g) 1 = 1 := by
  rw [actual_vacuum, scalar_eq_one, one_smul]

end

end Math.CompactSpin.ExteriorComparison
