import Math.Algebra.Lie.Sl3HighestWeight
import Math.Algebra.Lie.StandardSl3Borel
import Mathlib.Tactic

/-!
# Existence of dominant integral highest weights for `sl₃(ℂ)` modules

Lie's theorem applied to the concrete solvable upper Borel produces a common
eigenvector.  The simple-root commutator relations force the positive-root
eigenvalues to vanish, and the two `sl₂` triples force the Cartan eigenvalues
to be natural numbers.
-/

namespace Math
namespace Sl3HighestWeight

open LieModule
open StandardSl3

noncomputable section

def borelH1 : upperBorel := ⟨H1, H1_mem_upperBorel⟩
def borelH2 : upperBorel := ⟨H2, H2_mem_upperBorel⟩
def borelE1 : upperBorel := ⟨E1, E1_mem_upperBorel⟩
def borelE2 : upperBorel := ⟨E2, E2_mem_upperBorel⟩

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable [LieRingModule Algebra V] [LieModule ℂ Algebra V]
variable [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
private theorem lie_lie_eq_zero_of_common_eigenvector
    {v : V} {X Y : Algebra} {a b : ℂ}
    (hX : ⁅X, v⁆ = a • v) (hY : ⁅Y, v⁆ = b • v) :
    ⁅⁅X, Y⁆, v⁆ = 0 := by
  rw [lie_lie, hY, hX, lie_smul, lie_smul, hX, hY, smul_smul, smul_smul]
  rw [mul_comm a b, sub_self]

omit [FiniteDimensional ℂ V] in
private theorem simpleRootEigenvalue_eq_zero
    {v : V} {H E : Algebra} {mu lambda : ℂ}
    (hv : v ≠ 0) (hHE : ⁅H, E⁆ = (2 : ℂ) • E)
    (hH : ⁅H, v⁆ = mu • v) (hE : ⁅E, v⁆ = lambda • v) :
    lambda = 0 := by
  have hzero := lie_lie_eq_zero_of_common_eigenvector hH hE
  rw [hHE, smul_lie, hE, smul_smul] at hzero
  have hCoefficient : (2 : ℂ) * lambda = 0 :=
    (smul_eq_zero.mp hzero).resolve_right hv
  exact (mul_eq_zero.mp hCoefficient).resolve_left (by norm_num)

/-- Every nonzero finite-dimensional complex module for the concrete
`sl₃(ℂ)` has a dominant integral highest-weight vector. -/
theorem exists_highestWeightVector [Nontrivial V] :
    ∃ (a b : ℕ) (v : V), HighestWeightVector v a b := by
  let : LieModule.IsTriangularizable ℂ upperBorel V :=
    LieModule.instIsTriangularizableOfIsAlgClosed ℂ upperBorel V
  obtain ⟨chi, hWeightSpace⟩ :=
    LieModule.exists_nontrivial_weightSpace_of_isSolvable
      (k := ℂ) (L := upperBorel) (V := V)
  let : Nontrivial (LieModule.weightSpace V chi) := hWeightSpace
  obtain ⟨⟨v, hvWeight⟩, hv⟩ :=
    exists_ne (0 : LieModule.weightSpace V chi)
  have hv0 : v ≠ 0 := by
    simpa using hv
  have hAction (X : upperBorel) :
      ⁅(X : Algebra), v⁆ = chi X • v := by
    rw [LieModule.mem_weightSpace] at hvWeight
    simpa only [LieSubalgebra.coe_bracket_of_module] using hvWeight X
  have hH1 : ⁅H1, v⁆ = chi borelH1 • v := hAction borelH1
  have hH2 : ⁅H2, v⁆ = chi borelH2 • v := hAction borelH2
  have hE1Eigen : ⁅E1, v⁆ = chi borelE1 • v := hAction borelE1
  have hE2Eigen : ⁅E2, v⁆ = chi borelE2 • v := hAction borelE2
  have hE1Value : chi borelE1 = 0 :=
    simpleRootEigenvalue_eq_zero hv0
      (firstIsSl2Triple.lie_h_e_smul (R := ℂ)) hH1 hE1Eigen
  have hE2Value : chi borelE2 = 0 :=
    simpleRootEigenvalue_eq_zero hv0
      (secondIsSl2Triple.lie_h_e_smul (R := ℂ)) hH2 hE2Eigen
  have hE1 : ⁅E1, v⁆ = 0 := by rw [hE1Eigen, hE1Value, zero_smul]
  have hE2 : ⁅E2, v⁆ = 0 := by rw [hE2Eigen, hE2Value, zero_smul]
  have hFirstPrimitive :
      firstIsSl2Triple.HasPrimitiveVectorWith v (chi borelH1) :=
    { ne_zero := hv0
      lie_h := hH1
      lie_e := hE1 }
  have hSecondPrimitive :
      secondIsSl2Triple.HasPrimitiveVectorWith v (chi borelH2) :=
    { ne_zero := hv0
      lie_h := hH2
      lie_e := hE2 }
  obtain ⟨a, ha⟩ := hFirstPrimitive.exists_nat (R := ℂ)
  obtain ⟨b, hb⟩ := hSecondPrimitive.exists_nat (R := ℂ)
  refine ⟨a, b, v, ?_⟩
  exact
    { lie_H1 := by rw [hH1, ha]
      lie_H2 := by rw [hH2, hb]
      ne_zero := hv0
      lie_E1 := hE1
      lie_E2 := hE2 }

/-- Unconditional low-dimensional classification for nonzero irreducible
finite-dimensional modules over the concrete `sl₃(ℂ)`. -/
theorem finrank_eq_one_or_three_or_six
    [LieModule.IsIrreducible ℂ Algebra V]
    (hDimension : Module.finrank ℂ V ≤ 6) :
    Module.finrank ℂ V = 1 ∨ Module.finrank ℂ V = 3 ∨
      Module.finrank ℂ V = 6 := by
  let : Nontrivial V := LieModule.nontrivial_of_isIrreducible ℂ Algebra V
  obtain ⟨a, b, v, P⟩ := exists_highestWeightVector (V := V)
  exact finrank_eq_one_or_three_or_six_of_highestWeight P hDimension

end

end Sl3HighestWeight
end Math
