import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.Algebra.Lie.Weights.Dimension

/-!
# Dimension from a split Killing Lie algebra's roots

Compatibility wrapper for TauCeti's public dimension count. The local API uses
`Nat.card` of the root subtype instead of the cardinality of the root finset.
-/

set_option autoImplicit false

namespace Math.RootSpaceDimension

noncomputable section

open LieAlgebra LieModule Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- The zero weight contributes the Cartan dimension; every root contributes one. -/
theorem finrank_eq_cartan_add_card_root :
    finrank K L = finrank K H + Nat.card H.root := by
  classical
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    TauCeti.finrank_eq_finrank_cartan_add_card_root H

end

end Math.RootSpaceDimension
