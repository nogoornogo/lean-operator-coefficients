import Math.LieAlgebras.RootSpaceDimension
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.BaseChange

/-! # Numbered Cartan bases and dimensions of scalar-extended pinned Lie algebras -/

set_option autoImplicit false

namespace Math.PinnedGeckBasis

noncomputable section

open TauCeti RootPairing.GeckConstruction

attribute [local instance 100] LieRing.ofAssociativeRing

variable (t : DynkinType) (ht : t.Valid) (K : Type*) [Field K] [Algebra ℚ K]

local instance : CharZero K := Algebra.charZero_of_charZero ℚ K

def nodeEquiv : Fin t.rank ≃ (t.baseChangeBase ht K).support :=
  (t.simpleSupportEquiv ht).trans (t.supportBaseChangeEquiv ht K).symm

/-- Geck's basis after scalar extension, with the original Bourbaki numbering. -/
def numberedBasis : LieAlgebra.Basis (Fin t.rank)
    (cartanSubalgebra' (t.baseChangeBase ht K)) :=
  (basis (t.baseChangeBase ht K)).reindex (nodeEquiv t ht K).symm

@[simp] theorem numberedBasis_A : (numberedBasis t ht K).A = t.cartanMatrix := by
  ext i j
  simp only [numberedBasis, LieAlgebra.Basis.reindex_A, Matrix.submatrix_apply,
    Equiv.symm_symm, basis_A_eq]
  change (t.baseChangeBase ht K).cartanMatrix
    ((t.supportBaseChangeEquiv ht K).symm (t.simpleSupportEquiv ht i))
    ((t.supportBaseChangeEquiv ht K).symm (t.simpleSupportEquiv ht j)) = _
  rw [TauCeti.cartanMatrix_rootPairingBaseChangeBase]
  simp [DynkinType.supportBaseChangeEquiv]

variable [IsAlgClosed K]

instance : LieAlgebra.IsSimple K (t.lieAlgebraBaseChange ht K) :=
  inferInstanceAs (LieAlgebra.IsSimple K (lieAlgebra (t.baseChangeBase ht K)))

/-- Dimension of the actual Geck carrier, not just its ambient matrix index set. -/
theorem finrank_lieAlgebra :
    Module.finrank K (t.lieAlgebraBaseChange ht K) = t.rank + t.numRoots := by
  change Module.finrank K (lieAlgebra (t.baseChangeBase ht K)) = _
  rw [RootSpaceDimension.finrank_eq_cartan_add_card_root
    (cartanSubalgebra' (t.baseChangeBase ht K)), (numberedBasis t ht K).finrank_cartan]
  have hc := Nat.card_congr (equivRootSystem (t.baseChangeBase ht K)).indexEquiv
  rw [← hc]
  simp

end

end Math.PinnedGeckBasis
