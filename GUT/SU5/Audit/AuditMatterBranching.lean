import Math.Audit.ImportOrigin
import GUT.SU5.Branching.Unitary
import GUT.SU5.Representations.MatterIrreducibility

open Physics

open Math

/-! Persistent tests for actual matter branching, analytic realization, and
SU(5) irreducibility. Irreducibility is proved, not an input hypothesis;
it is not asserted for the restricted SM actions. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU6).isPrefixOf mod then
      throwError "SU(5) matter audit imports SU(6): {mod}"

namespace GUT.SU5.AuditMatterBranching

noncomputable section

open StandardModelEmbedding StandardSMGaugeTensor SMEpsilonTensor

theorem actual_dimensions :
    Module.finrank ℂ Matter.Five = 5 ∧ Module.finrank ℂ Matter.BarFive = 5 ∧
    Module.finrank ℂ Matter.Ten = 10 ∧ Module.finrank ℂ UnitaryMatter.TenHilbert = 10 :=
  ⟨Matter.five_finrank, Matter.barFive_finrank, Matter.ten_finrank,
    UnitaryMatter.tenHilbert_finrank⟩

theorem ten_branch_inverse (x : Matter.Ten) :
    ExteriorSquareBranching.tenEquiv.symm (ExteriorSquareBranching.tenEquiv x) = x :=
  ExteriorSquareBranching.tenEquiv.toLinearEquiv.symm_apply_apply x

theorem ten_branch_inverse_right (x : ExteriorSquareBranching.Blocks) :
    ExteriorSquareBranching.tenEquiv (ExteriorSquareBranching.tenEquiv.symm x) = x :=
  ExteriorSquareBranching.tenEquiv.toLinearEquiv.apply_symm_apply x

/-- The mixed wedge lands in Q with a positive orientation. -/
theorem mixed_wedge_sign :
    ExteriorSquareBranching.branch
        (ExteriorSquareBranching.wedge (![1, 0, 0], 0) (0, ![1, 0])) =
      (0, (![1, 0, 0] ⊗ₜ[ℂ] ![1, 0], 0)) := by
  simp

/-- The weak wedge is e^c, not the right-handed electron. -/
theorem weak_wedge_sign :
    ExteriorSquareBranching.branch
        (ExteriorSquareBranching.wedge (0, ![1, 0]) (0, ![0, 1])) =
      (0, (0, (LinearMap.id : ℂ →ₗ[ℂ] ℂ))) := by
  simp [eps2]

theorem color_wedge_sign :
    (ExteriorSquareBranching.branch
      (ExteriorSquareBranching.wedge (![1, 0, 0], 0) (![0, 1, 0], 0))).1
        ![0, 0, 1] = 1 := by
  rw [ExteriorSquareBranching.branch_wedge_split, ExteriorSquareBranching.pair_color_color]
  change eps3 ![1, 0, 0] ![0, 1, 0] ![0, 0, 1] = 1
  norm_num [eps3]

theorem reversed_weak_wedge_sign :
    ExteriorSquareBranching.branch
        (ExteriorSquareBranching.wedge (0, ![0, 1]) (0, ![1, 0])) =
      (0, (0, -(LinearMap.id : ℂ →ₗ[ℂ] ℂ))) := by
  simp [eps2]

private theorem phase_apply (y : ℤ) (g : GaugeGroup) :
    phase y g = (↑(g.2.2 ^ y) : ℂ) := rfl

theorem pure_circle_up (z : Circle) (phi : Module.Dual ℂ Color) :
    upRight.dual (1, 1, z) phi = (↑(z ^ (-4 : ℤ)) : ℂ) • phi := by
  apply LinearMap.ext; intro v
  simp [Representation.dual, upRight, twist, color, phase_apply]

theorem pure_circle_down (z : Circle) (phi : Module.Dual ℂ Color) :
    downRight.dual (1, 1, z) phi = (↑(z ^ (2 : ℤ)) : ℂ) • phi := by
  apply LinearMap.ext; intro v
  simp [Representation.dual, downRight, twist, color, phase_apply]

theorem pure_circle_electron (z : Circle) (phi : Module.Dual ℂ ℂ) :
    electronRight.dual (1, 1, z) phi = (↑(z ^ (6 : ℤ)) : ℂ) • phi := by
  apply LinearMap.ext; intro v
  have hphi (a b : ℂ) : phi (a * b) = a * phi b := phi.map_smul a b
  simp [Representation.dual, electronRight, twist, phase_apply, hphi]

theorem pure_circle_quark (z : Circle) (q : Quark) :
    quark (1, 1, z) q = (z : ℂ) • q := by
  simp [quark, twist, color, weak, phase_apply]

theorem pure_circle_lepton (z : Circle) (v : Weak) :
    lepton (1, 1, z) v = (↑(z ^ (-3 : ℤ)) : ℂ) • v := by
  simp [lepton, twist, weak, phase_apply]

theorem all_kernel_elements_act_trivially (g : GaugeGroup) (hg : g ∈ hom.ker) :
    FundamentalBranching.barBlocksRho g = 1 ∧ ExteriorSquareBranching.blocksRho g = 1 :=
  ⟨QuotientDescent.kernel_acts_trivially FundamentalBranching.antifundamentalEquiv g hg,
    QuotientDescent.kernel_acts_trivially ExteriorSquareBranching.tenEquiv g hg⟩

theorem quotient_recovers_ten (g : GaugeGroup) :
    QuotientDescent.ten (QuotientGroup.mk g) = ExteriorSquareBranching.blocksRho g := rfl

theorem quotient_recovers_barFive (g : GaugeGroup) :
    QuotientDescent.barFive (QuotientGroup.mk g) = FundamentalBranching.barBlocksRho g := rfl

example : Continuous UnitaryMatter.ten := UnitaryMatter.ten_continuous
example : ContRepresentation.IsUnitary UnitaryMatter.ten := UnitaryMatter.ten_unitary
example : Continuous UnitaryBranching.quotientTen := UnitaryBranching.quotientTen_continuous
example : ContRepresentation.IsUnitary UnitaryBranching.quotientTen :=
  UnitaryBranching.quotientTen_unitary

theorem actual_matter_irreducible :
    Matter.fundamental.IsIrreducible ∧ Matter.antifundamental.IsIrreducible ∧
      Matter.ten.IsIrreducible :=
  ⟨MatterIrreducibility.fundamental_irreducible,
    MatterIrreducibility.antifundamental_irreducible, MatterIrreducibility.ten_irreducible⟩

theorem unitary_matter_irreducible :
    UnitaryMatter.fundamental.toRepresentation.IsIrreducible ∧
    UnitaryMatter.antifundamental.toRepresentation.IsIrreducible ∧
    UnitaryMatter.ten.toRepresentation.IsIrreducible :=
  ⟨MatterIrreducibility.unitary_fundamental_irreducible,
    MatterIrreducibility.unitary_antifundamental_irreducible,
    MatterIrreducibility.unitary_ten_irreducible⟩

theorem ten_subrepresentations (S : Subrepresentation Matter.ten) : S = ⊥ ∨ S = ⊤ := by
  let : Matter.ten.IsIrreducible := MatterIrreducibility.ten_irreducible
  exact eq_bot_or_eq_top S

theorem barFive_subrepresentations (S : Subrepresentation Matter.antifundamental) :
    S = ⊥ ∨ S = ⊤ := by
  let : Matter.antifundamental.IsIrreducible := MatterIrreducibility.antifundamental_irreducible
  exact eq_bot_or_eq_top S

example : IsEmpty (Representation.Equiv UnitaryMatter.ten.toRepresentation
    UnitaryMatter.antifundamental.toRepresentation) :=
  MatterIrreducibility.unitary_ten_not_equiv_barFive

#print axioms Math.RepresentationTheory.irreducible_of_basis_coordinates
#print axioms MonomialElements.diagonalSign
#print axioms MonomialElements.signedPermutation
#print axioms MatterIrreducibility.antifundamental_project
#print axioms MatterIrreducibility.tenProject_eq
#print axioms MatterIrreducibility.ten_basis_transitive
#print axioms MatterIrreducibility.fundamental_irreducible
#print axioms MatterIrreducibility.antifundamental_irreducible
#print axioms MatterIrreducibility.ten_irreducible
#print axioms MatterIrreducibility.unitary_fundamental_irreducible
#print axioms MatterIrreducibility.unitary_antifundamental_irreducible
#print axioms MatterIrreducibility.unitary_ten_irreducible
#print axioms MatterIrreducibility.unitary_ten_not_equiv_barFive
#print axioms actual_matter_irreducible
#print axioms unitary_matter_irreducible
#print axioms ten_subrepresentations
#print axioms barFive_subrepresentations
#print axioms FiniteBasisUnitaryModel.modelEquiv
#print axioms FiniteBasisUnitaryModel.model_jointlyContinuous
#print axioms UnitaryMatter.fundamentalEquiv
#print axioms UnitaryMatter.antifundamentalEquiv
#print axioms UnitaryMatter.tenEquiv
#print axioms UnitaryMatter.fundamental_unitary
#print axioms UnitaryMatter.antifundamental_unitary
#print axioms UnitaryMatter.ten_unitary
#print axioms FundamentalBranching.fundamentalEquiv
#print axioms FundamentalBranching.antifundamentalEquiv
#print axioms ExteriorSquareBranching.tenEquiv
#print axioms UnitaryBranching.quotientTenEquiv
#print axioms UnitaryBranching.quotientBarFiveEquiv
#print axioms UnitaryBranching.quotientTen_continuous
#print axioms UnitaryBranching.quotientTen_unitary
#print axioms Matter.ten_not_equiv_barFive
#print axioms actual_dimensions
#print axioms ten_branch_inverse
#print axioms ten_branch_inverse_right
#print axioms mixed_wedge_sign
#print axioms weak_wedge_sign
#print axioms color_wedge_sign
#print axioms reversed_weak_wedge_sign
#print axioms pure_circle_up
#print axioms pure_circle_down
#print axioms pure_circle_electron
#print axioms pure_circle_quark
#print axioms pure_circle_lepton
#print axioms all_kernel_elements_act_trivially
#print axioms quotient_recovers_ten
#print axioms quotient_recovers_barFive

end

end GUT.SU5.AuditMatterBranching
