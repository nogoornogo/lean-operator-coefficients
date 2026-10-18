import Math.RepresentationTheory.ComplementaryExteriorDuality
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! Exterior powers commute equivariantly with algebraic duality in finite
dimension. The underlying perfect pairing is mathlib's proved pairingDual;
only its representation-theoretic naturality is added here. -/
namespace Math.ExteriorDualEquivalence
set_option autoImplicit false
noncomputable section
open Representation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  (rho : Representation ℂ G V) (n : ℕ)

def pairing : IntertwiningMap (rho.dual.exteriorPower n) (rho.exteriorPower n).dual where
  toLinearMap := exteriorPower.pairingDual ℂ V n
  isIntertwining' g := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro f
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change exteriorPower.pairingDual ℂ V n
        (rho.dual.exteriorPower n g (exteriorPower.ιMulti ℂ n f))
        (exteriorPower.ιMulti ℂ n v)=
      exteriorPower.pairingDual ℂ V n (exteriorPower.ιMulti ℂ n f)
        (rho.exteriorPower n g⁻¹ (exteriorPower.ιMulti ℂ n v))
    rw [Representation.exteriorPower_apply_ιMulti, Representation.exteriorPower_apply_ιMulti,
      exteriorPower.pairingDual_ιMulti_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti]
    rfl

variable [FiniteDimensional ℂ V]

/-- Complete actual dual/exterior equivalence. Bijectivity is the existing
mathlib theorem, uniformly in the exterior degree; no basis is evaluated. -/
def equivalence : Representation.Equiv (rho.dual.exteriorPower n) (rho.exteriorPower n).dual :=
  (pairing rho n).ofBijective (exteriorPower.bijective_pairingDual ℂ V n)

end
end Math.ExteriorDualEquivalence
