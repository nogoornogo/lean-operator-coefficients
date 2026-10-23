import Math.Algebra.Jets.MixedJetAlgebra
import Math.LinearAlgebra.Exterior.ExteriorLeftDerivative

/-! Coordinate extraction by two Grassmann contractions. These contractions
are probes, distinct from the even spacetime total derivative. -/
namespace Math.MixedJetAlgebra
set_option autoImplicit false
noncomputable section
open JetLinear ScalarJetAlgebra

variable {F I : Type*}

def pairCoordinate (j k : Index F I) : Odd F I →ₗ[ℂ] ℂ :=
  ExteriorAlgebra.algebraMapInv.toLinearMap.comp
    ((ExteriorLeftDerivative.derivative (Finsupp.lapply k)).comp
      (ExteriorLeftDerivative.derivative (Finsupp.lapply j)))

theorem pairCoordinate_ι_mul (j k : Index F I) (u v : Jet F I) :
    pairCoordinate j k (ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v) =
      u j * v k - v j * u k := by
  simp [pairCoordinate, ExteriorLeftDerivative.derivative,
    CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι,
    CliffordAlgebra.contractLeft_mul_algebraMap, mul_comm]

end
end Math.MixedJetAlgebra
