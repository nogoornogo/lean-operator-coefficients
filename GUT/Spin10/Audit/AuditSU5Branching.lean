import Math.Audit.ImportOrigin
import GUT.Spin10.SU5Branching
import GUT.SU5.Embeddings.MaximalTorus

open Math Math.SU5

/-! Full-group half-spin character branching and an orientation-sensitive
diagonal control. SU(5) matter imports are now intentional; SU(6)/USp are not. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU6).isPrefixOf mod || (`GUT.Sp).isPrefixOf mod then
      throwError "Spin branching imports another ambient gauge family: {mod}"

namespace GUT.CompactSpin.AuditSU5Branching

open Math.CompactSpin
noncomputable section

open GUT.SU5

def quarterTurn : Circle := ⟨Complex.I, mem_sphere_zero_iff_norm.mpr (by simp)⟩

@[simp] theorem coe_quarterTurn : (quarterTurn : ℂ) = Complex.I := rfl

@[simp] theorem coe_neg_quarterTurn : ((-quarterTurn : Circle) : ℂ) = -Complex.I :=
  Circle.coe_neg quarterTurn

def probe : CompactSpin.SU5 :=
  MaximalTorus.diagonalElement ![quarterTurn, quarterTurn, quarterTurn, -quarterTurn, -1] (by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    change quarterTurn * (quarterTurn * (quarterTurn * (-quarterTurn * (-1)))) = 1
    apply Circle.coe_injective
    simp only [Circle.coe_mul, Circle.coe_neg, Circle.coe_one]
    change Complex.I * (Complex.I * (Complex.I * (-Complex.I * (-1)))) = 1
    norm_num)

theorem fundamental_probe : Matter.fundamental.character probe = -1 + 2 * Complex.I := by
  simp [Representation.character, Matter.fundamental, probe, MaximalTorus.diagonalElement,
    Matrix.trace, Fin.sum_univ_succ]
  ring

theorem antifundamental_probe : Matter.antifundamental.character probe = -1 - 2 * Complex.I := by
  rw [Matter.antifundamental, Representation.char_dual]
  change LinearMap.trace ℂ Matter.Five (Matrix.toLin' (star probe.val)) = _
  simp [probe, MaximalTorus.diagonalElement,
    Matrix.trace, Fin.sum_univ_succ,
    Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  ring

/-- The degree-four contribution is bar-five, not five. -/
theorem wrong_degree_four_rejected :
    (HalfSpin.representation 5).character (SU5Inclusion probe) ≠
      1 + Matter.ten.character probe + Matter.fundamental.character probe := by
  rw [SU5Branching.halfSpin_character]
  intro h
  have he := add_left_cancel h
  rw [fundamental_probe, antifundamental_probe] at he
  have hi := congrArg Complex.im he
  norm_num at hi

example (g : CompactSpin.SU5) :
    (HalfSpin.unitaryModel 5).toRepresentation.character (SU5Inclusion g) =
      1 + UnitaryMatter.ten.toRepresentation.character g +
        UnitaryMatter.antifundamental.toRepresentation.character g := SU5Branching.unitary_character g

example : Fintype.card HalfSpinEigenbasis.Index = 16 := HalfSpinEigenbasis.card_index

#print axioms HalfSpinEigenbasis.card_index
#print axioms HalfSpinEigenbasis.independent
#print axioms HalfSpinEigenbasis.basis
#print axioms HalfSpinEigenbasis.eigen
#print axioms HalfSpinEigenbasis.character
#print axioms SU5Branching.exists_fundamental_eigenbasis
#print axioms SU5Branching.product_eigenvalues
#print axioms SU5Branching.halfSpin_character
#print axioms SU5Branching.unitary_character
#print axioms SU5Branching.unitary_dual_index
#print axioms fundamental_probe
#print axioms antifundamental_probe
#print axioms wrong_degree_four_rejected

end

end GUT.CompactSpin.AuditSU5Branching
