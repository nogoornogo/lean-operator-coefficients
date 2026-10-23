import Physics.FieldTheory.Jets.Weyl.Equations.WeylEquationIBP
import Math.Algebra.Jets.LinearJetSingleField

/-! Complete positive-derivative single-Weyl EOM/IBP source in four dimensions. -/
namespace Physics.WeylSingleFieldIBP
set_option autoImplicit false
noncomputable section
open Math WeylLinearEquation

abbrev Source (d : ℕ) := LinearJetAlgebra.grade seed spectatorSeed 1 0 (d + 1)
@[reducible] local instance (d : ℕ) : AddCommGroup (Source d) := inferInstance
@[reducible] local instance (d : ℕ) : Module ℂ (Source d) := inferInstance
abbrev Relations (d : ℕ) := LinearJetAlgebra.ibpRelations seed spectatorSeed 1 0 d
abbrev Quotient (d : ℕ) := Source d ⧸ Relations d

def action (d : ℕ) := LinearJetAlgebra.quotientAction seed spectatorSeed
  WeylSpinor.right.dual spectatorEquations (LorentzJetIBP.weyl false) LorentzJetIBP.scalarField
  LorentzDirections.direction seed_covariant spectator_covariant 1 0 d

theorem relations_top (d : ℕ) : Relations d = ⊤ := LinearJetAlgebra.odd_ibpRelations_top _ _ d

theorem quotient_zero (d : ℕ) (x : Quotient d) : x = 0 := Subsingleton.elim _ _

theorem dimension (d : ℕ) : Module.finrank ℂ (Quotient d) = 0 :=
  LinearJetAlgebra.odd_quotient_finrank _ _ d

def basis (d : ℕ) : Module.Basis (Fin 0) ℂ (Quotient d) :=
  LinearJetAlgebra.odd_quotient_basis _ _ d

theorem coefficient_zero (d : ℕ)
    (f : Representation.IntertwiningMap (action d) (Representation.trivial ℂ Group ℂ)) : f = 0 := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change f x = 0
  rw [quotient_zero d x, map_zero]

private def offFirst : MixedJetAlgebra.grade (Fin 2) Unit (Fin 4) 1 0 1 :=
  ⟨MixedJetAlgebra.odd (1, Finsupp.single 0 1), by
    simpa [ScalarJetAlgebra.order, Finsupp.weight_single] using
      (MixedJetAlgebra.odd_mem (B := Unit) (1, Finsupp.single (0 : Fin 4) 1))⟩

def firstJet : Source 0 := LinearJetAlgebra.gradeProjection seed spectatorSeed 1 0 1 offFirst

theorem firstJet_nonzero : firstJet ≠ 0 := by
  intro hz
  have he := congrArg Subtype.val hz
  have hn := higher_mixed_jet_survives 1
  apply hn
  change projection (MixedJetAlgebra.odd (1, Finsupp.single 0 1)) = 0 at he
  simpa [pow_one, JetFunctor.oddVector, MixedJetAlgebra.odd,
    MvPolynomial.X, JetDirections.ofSymbols_monomial] using he

theorem firstJet_ibp_zero : (Relations 0).mkQ firstJet = 0 := quotient_zero 0 _

end
end Physics.WeylSingleFieldIBP
