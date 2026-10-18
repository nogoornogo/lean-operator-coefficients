import Math.RepresentationTheory.OccupationExteriorDecomposition
import Math.RepresentationTheory.PatternCountSum
import Math.RepresentationTheory.TorusScalarProductSlice

/-! Scalar species weights descend to the actual statistical source, and
the exponent is its occupation-weight sum. This is an action identity,
not a character calculation. -/
namespace Math.PatternScalarWeights
set_option autoImplicit false
noncomputable section
open Representation PatternExteriorSource FiniteExteriorExhaustion
variable {S G K : Type*} [Fintype S] [DecidableEq S] [Group G] [Group K]
  {V : S → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  (r : ∀ s, Representation ℂ (G × K) (V s)) (t : Circle →* G)
  (w : S → ℤ)
  (hw : ∀ s z x, r s (t z,1) x=(z : ℂ)^(w s) • x)
  {n : ℕ} (p : Fin n → S)

omit [Fintype S] [DecidableEq S] in
include hw in
theorem raw_scalar (z : Circle) :
    Raw r p (t z,1)=(z : ℂ)^(∑ i, w (p i)) • LinearMap.id := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply,
    MultilinearInvariantHom.tensorRepresentation_tprod, hw,
    LinearMap.smul_apply, LinearMap.id_apply]
  rw [← ExteriorWeightSupport.prod_zpow (z : ℂ) z.coe_ne_zero]
  exact (PiTensorProduct.tprod ℂ).map_smul_univ _ v

include hw in
theorem source_scalar (z : Circle) (x : Source r p) :
    representation r p (t z,1) x=(z : ℂ)^(∑ i, w (p i)) • x :=
  PatternExteriorSource.source_scalar r p (t z,1) _ (raw_scalar r t w hw p z) x

def occupationWeight (n : ℕ) (c : Occupation (S := S) n) : ℤ :=
  ∑ s, (c.val s).val • w s

theorem representative_weight (n : ℕ) (c : Occupation (S := S) n) :
    ∑ i, w (representative n c i)=occupationWeight w n c := by
  rw [PatternCountSum.sum_weights]
  apply Finset.sum_congr rfl
  intro s _
  rw [← representative_counts n c]
  rfl

include hw in
theorem occupation_scalar (n : ℕ) (c : Occupation (S := S) n)
    (z : Circle) (x : OccupationExteriorDecomposition.Carrier r n c) :
    OccupationExteriorDecomposition.block r n c (t z,1) x=
      (z : ℂ)^(occupationWeight w n c) • x := by
  rw [← representative_weight w n c]
  exact source_scalar r t w hw _ z x

/-- If the selected occupation has a unique weight, the actual exterior
weight space is precisely that entire occupation representation. -/
def equivalence (n : ℕ) (c : Occupation (S := S) n)
    (hc : ∀ d, occupationWeight w n d=occupationWeight w n c → d=c) :
    Representation.Equiv
      (TorusWeightSlice.action (Full r (n := n)) t (occupationWeight w n c))
      (TorusWeightSlice.residual (OccupationExteriorDecomposition.block r n c)) := by
  let : DecidableEq (Occupation (S := S) n) := Classical.decEq _
  exact (TorusWeightSlice.transport (Full r (n := n)) t
    (OccupationExteriorDecomposition.equivalence r n) _).trans
      (TorusScalarProductSlice.equivalence (OccupationExteriorDecomposition.block r n)
        t (occupationWeight w n) c (hw := occupation_scalar r t w hw n) (hj := hc))

include hw in
theorem absent_zero (n : ℕ) (k : ℤ) (hk : ∀ c, occupationWeight w n c≠k)
    (x : TorusWeightSlice.Space (Full r (n := n)) t k) : x=0 := by
  let e := TorusWeightSlice.transport (Full r (n := n)) t
    (OccupationExteriorDecomposition.equivalence r n) k
  apply e.injective
  rw [map_zero]
  exact TorusScalarProductSlice.absent_zero (OccupationExteriorDecomposition.block r n)
    t (occupationWeight w n) (occupation_scalar r t w hw n) k hk (e x)

end
end Math.PatternScalarWeights
