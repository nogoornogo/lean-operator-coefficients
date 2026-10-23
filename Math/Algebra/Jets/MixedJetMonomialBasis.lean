import Math.Algebra.Jets.MixedJetAlgebra
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.SetTheory.Cardinal.Order

/-! An actual basis at every field number and derivative order. Ordering is
only a coordinate choice on odd jets, not an extra physical assumption. -/
namespace Math.MixedJetMonomialBasis
set_option autoImplicit false
noncomputable section
open ScalarJetAlgebra

abbrev Monomial (F B I : Type*) := Finset (Index F I) × (Index B I →₀ ℕ)

@[instance_reducible] def oddOrder (F I : Type*) : LinearOrder (Index F I) :=
  IsWellOrder.linearOrder WellOrderingRel

def basis (F B I : Type*) : Module.Basis (Monomial F B I) ℂ (MixedJetAlgebra.Algebra F B I) := by
  letI := oddOrder F I
  exact (Finsupp.basisSingleOne.ExteriorAlgebra).tensorProduct
    (MvPolynomial.basisMonomials (Index B I) ℂ)

end
end Math.MixedJetMonomialBasis
