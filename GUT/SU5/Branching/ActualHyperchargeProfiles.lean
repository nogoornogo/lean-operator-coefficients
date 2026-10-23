import GUT.SU5.Branching.CyclicHypercharge
import Math.LinearAlgebra.Exterior.ExteriorEigenbasisTrace
import Math.LinearAlgebra.Constructions.EigenbasisTrace
import Mathlib.Data.Sum.Order

-- Check finite certificates sequentially to avoid blocked elaboration worker stacks.
set_option Elab.async false

namespace GUT.SU5.ActualHyperchargeProfiles
set_option autoImplicit false
noncomputable section
open Math Representation Matter StandardModelEmbedding
open FortyHyperchargeExclusion ExoticHyperchargeBasis
open scoped BigOperators TensorProduct
local instance : LinearOrder FiveIndex := LinearOrder.lift'
  finSumFinEquiv finSumFinEquiv.injective
local instance : AddCommGroup Ten := inferInstance
local instance : AddCommGroup ExoticSymmetricKernel.kernel.toSubmodule := inferInstance

def five : CyclicHypercharge.Polynomial :=
  ∑ i : FiveIndex, Finsupp.single (fiveWeight i : ZMod 31) 1
def tenProfile : CyclicHypercharge.Polynomial :=
  ∑ i : Index, Finsupp.single (weight i : ZMod 31) 1
def exterior (d : ℕ) : CyclicHypercharge.Polynomial :=
  ∑ s ∈ (Finset.univ : Finset FiveIndex).powersetCard d,
    Finsupp.single ((∑ i ∈ s, fiveWeight i : ℤ) : ZMod 31) 1
theorem exterior_subtype (d : ℕ) : exterior d =
    ∑ s : Set.powersetCard FiveIndex d,
      Finsupp.single ((∑ i ∈ s.val, fiveWeight i : ℤ) : ZMod 31) 1 := by
  apply Finset.sum_subtype
  intro s
  simp [Set.powersetCard]

def symmetric : CyclicHypercharge.Polynomial :=
  ∑ s ∈ (Finset.univ : Finset Index).sym 2,
    Finsupp.single (((s : Multiset Index).map weight).sum : ZMod 31) 1

theorem symmetric_univ : symmetric = ∑ s : Sym Index 2,
    Finsupp.single (((s : Multiset Index).map weight).sum : ZMod 31) 1 := by
  have he : (Finset.univ : Finset Index).sym 2 = Finset.univ := Finset.sym_univ 2
  unfold symmetric
  rw [he]

theorem five_character (g : CyclicHypercharge.Group) :
    fundamental.character (hom (1,1,CyclicHypercharge.circle g)) = CyclicHypercharge.eval five g := by
  change LinearMap.trace ℂ Five _ = _
  rw [WeightTheory.trace_eq_sum_of_basis_eigen fiveBasis _ _ (five_basis_action _)]
  simp [five, CyclicHypercharge.eval_sum, CyclicHypercharge.character_integer]

theorem ten_character (g : CyclicHypercharge.Group) :
    ten.character (hom (1,1,CyclicHypercharge.circle g)) = CyclicHypercharge.eval tenProfile g := by
  change LinearMap.trace ℂ Ten _ = _
  rw [WeightTheory.trace_eq_sum_of_basis_eigen tenBasis _ _ (basis_action _)]
  simp [tenProfile, CyclicHypercharge.eval_sum, CyclicHypercharge.character_integer]

theorem exterior_character (d : ℕ) (g : CyclicHypercharge.Group) :
    (fundamental.exteriorPower d).character (hom (1,1,CyclicHypercharge.circle g)) =
      CyclicHypercharge.eval (exterior d) g := by
  change LinearMap.trace ℂ (⋀[ℂ]^d Five) (exteriorPower.map d _) = _
  rw [ExteriorEigenbasisTrace.exterior_trace fiveBasis _ _ (five_basis_action _) d]
  simp only [exterior_subtype, CyclicHypercharge.eval_sum, CyclicHypercharge.eval_single, Int.cast_one, one_mul,
    CyclicHypercharge.character_integer]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Circle.coe_zpow]
  have hp (u : Finset FiveIndex) :
      ∏ i ∈ u, (CyclicHypercharge.circle g : ℂ)^fiveWeight i =
        (CyclicHypercharge.circle g : ℂ)^(∑ i ∈ u, fiveWeight i) := by
    induction u using Finset.induction_on with
    | empty => simp
    | @insert i u hi ih =>
      simp [hi, ih, zpow_add₀ (Circle.coe_ne_zero (CyclicHypercharge.circle g))]
  exact hp s.val

theorem coefficient_sum (z : Circle) (s : Sym Index 2) :
    ExoticHyperchargeBasis.coefficient z s = ((z^((s : Multiset Index).map weight).sum : Circle) : ℂ) := by
  unfold ExoticHyperchargeBasis.coefficient
  induction (s : Multiset Index) using Multiset.induction_on with
  | empty => simp
  | @cons i t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    rw [ih]
    simp only [zpow_add, Circle.coe_mul]

theorem symmetric_character (g : CyclicHypercharge.Group) :
    (ten.symmetricPower 2).character (hom (1,1,CyclicHypercharge.circle g)) =
      CyclicHypercharge.eval symmetric g := by
  change LinearMap.trace ℂ (Sym[ℂ]^2 Ten) _ = _
  rw [WeightTheory.trace_eq_sum_of_basis_eigen symmetricBasis _ _ (symmetric_action _)]
  simp only [symmetric_univ, CyclicHypercharge.eval_sum, CyclicHypercharge.eval_single,
    Int.cast_one, one_mul, CyclicHypercharge.character_integer, coefficient_sum]

def fortyOriginal : CyclicHypercharge.Polynomial :=
  ∑ i : FiveIndex × Index,
    Finsupp.single ((fiveWeight i.1 + weight i.2 : ℤ) : ZMod 31) 1
def fortyProfile : CyclicHypercharge.Polynomial :=
  CyclicHypercharge.dual (fortyOriginal - exterior 3)
def fiftyProfile : CyclicHypercharge.Polynomial := symmetric - exterior 4

theorem five_coefficients : five = Finsupp.single (-2) 3 + Finsupp.single 3 2 := by
  apply Finsupp.ext
  intro k
  simp only [five, Finsupp.add_apply, Finset.sum_apply', Finsupp.single_apply]
  revert k
  decide +kernel
theorem ten_coefficients : tenProfile =
    Finsupp.single (-4) 3 + Finsupp.single 1 6 + Finsupp.single 6 1 := by
  apply Finsupp.ext
  intro k
  simp only [tenProfile, Finsupp.add_apply, Finset.sum_apply', Finsupp.single_apply]
  revert k
  decide +kernel
theorem exterior_three_coefficients : exterior 3 =
    Finsupp.single (-6) 1 + Finsupp.single (-1) 6 + Finsupp.single 4 3 := by
  apply Finsupp.ext
  intro k
  simp only [exterior, Finsupp.add_apply, Finset.sum_apply', Finsupp.single_apply]
  revert k
  decide +kernel
theorem exterior_four_coefficients : exterior 4 =
    Finsupp.single (-3) 2 + Finsupp.single 2 3 := by
  apply Finsupp.ext
  intro k
  simp only [exterior, Finsupp.add_apply, Finset.sum_apply', Finsupp.single_apply]
  revert k
  decide +kernel
theorem forty_coefficients : fortyProfile =
    Finsupp.single 6 8 + Finsupp.single 1 18 + Finsupp.single (-4) 12 + Finsupp.single (-9) 2 := by
  apply Finsupp.ext
  intro k
  simp only [fortyProfile, fortyOriginal, exterior, CyclicHypercharge.dual_apply, Finsupp.sub_apply, Finsupp.add_apply, Finset.sum_apply', Finsupp.single_apply]
  revert k
  decide +kernel
theorem fifty_coefficients : fiftyProfile =
    Finsupp.single (-8) 6 + Finsupp.single (-3) 16 + Finsupp.single 2 21 +
      Finsupp.single 7 6 + Finsupp.single 12 1 := by
  apply Finsupp.ext
  intro k
  simp only [fiftyProfile, symmetric, exterior, Finsupp.sub_apply, Finsupp.add_apply, Finset.sum_apply', Finsupp.single_apply]
  revert k
  decide +kernel

theorem original_ambient_character (g : CyclicHypercharge.Group) :
    (fundamental.tprod ten).character (hom (1,1,CyclicHypercharge.circle g)) =
      CyclicHypercharge.eval fortyOriginal g := by
  change LinearMap.trace ℂ (Five ⊗[ℂ] Ten) _ = _
  rw [WeightTheory.trace_eq_sum_of_basis_eigen ambientBasis _ _ (ambient_action _)]
  simp only [fortyOriginal, CyclicHypercharge.eval_sum, CyclicHypercharge.eval_single,
    Int.cast_one, one_mul, CyclicHypercharge.character_integer, FortyHyperchargeExclusion.coefficient]

theorem forty_character (g : CyclicHypercharge.Group) :
    ExoticWedgeKernel.representation.character (hom (1,1,CyclicHypercharge.circle g)) =
      CyclicHypercharge.eval fortyProfile g := by
  rw [ExoticWedgeKernel.representation_character]
  have hh : (hom (1,1,CyclicHypercharge.circle g))⁻¹ = hom (1,1,CyclicHypercharge.circle g⁻¹) := by
    exact (map_inv hom (1,1,CyclicHypercharge.circle g)).symm.trans
      (congrArg hom (by simp))
  rw [hh, original_ambient_character, exterior_character]
  exact (CyclicHypercharge.eval_sub _ _ g⁻¹).symm.trans (CyclicHypercharge.eval_dual _ g).symm

theorem fifty_character (g : CyclicHypercharge.Group) :
    ExoticSymmetricKernel.representation.character (hom (1,1,CyclicHypercharge.circle g)) =
      CyclicHypercharge.eval fiftyProfile g := by
  rw [ExoticSymmetricKernel.kernel_character, symmetric_character, exterior_character]
  exact (CyclicHypercharge.eval_sub _ _ g).symm

end
end GUT.SU5.ActualHyperchargeProfiles
