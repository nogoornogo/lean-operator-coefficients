import Physics.FieldTheory.Spinor.Weyl.RightWeylChargeConjugation
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic

/-! Two-spin-component Grassmann mass action. The left-handed field dictionary
and kinetic action are supplied; no four-component charge-conjugation bridge. -/
namespace Physics.WeylGrassmannAction
set_option autoImplicit false
noncomputable section
variable {I : Type*}
abbrev Coordinates (I : Type*) := I × Fin 2 → ℂ
abbrev Algebra (I : Type*) := ExteriorAlgebra ℂ (Coordinates I)

def generator [DecidableEq I] (i : I) (s : Fin 2) : Algebra I :=
  ExteriorAlgebra.ι ℂ (Pi.single (i,s) 1)

def pair [DecidableEq I] (i j : I) : Algebra I :=
  generator i 0 * generator j 1 - generator i 1 * generator j 0

theorem generator_swap [DecidableEq I] (i j : I) (s t : Fin 2) :
    generator i s * generator j t = -(generator j t * generator i s) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

theorem pair_symmetric [DecidableEq I] (i j : I) : pair i j = pair j i := by
  unfold pair
  rw [generator_swap i j 0 1, generator_swap i j 1 0]
  abel

/-- Grassmann-valued extension of the existing Euclidean right-block embedding. -/
def rightComponents [DecidableEq I] (i : I) : Fin 4 → Algebra I :=
  ![generator i 0, generator i 1, 0, 0]

def fourPair [DecidableEq I] (i j : I) : Algebra I :=
  ∑ a, ∑ b,
    (Physics.RightWeylChargeConjugation.charge *
      Physics.RightWeylChargeConjugation.rightProjector) a b •
        (rightComponents i a * rightComponents j b)

/-- The fixed Euclidean CP_R convention has no extra sqrt(2) factor. -/
theorem four_component_right [DecidableEq I] (i j : I) : fourPair i j = pair i j := by
  simp [fourPair, rightComponents, pair, Physics.RightWeylChargeConjugation.charge,
    Physics.RightWeylChargeConjugation.rightProjector, Matrix.mul_apply,
    Fin.sum_univ_succ, sub_eq_add_neg]

def action (m : Matrix (Fin 3) (Fin 3) ℂ) : Algebra (Fin 3) :=
  (- (1/2 : ℂ)) • ∑ i, ∑ j, m i j • pair i j

/-- The off-diagonal factor two cancels the mass-action half because the
fermionic epsilon contraction is symmetric in species. -/
theorem three_species_action (d M mu : ℂ) :
    action !![0,d,0;d,0,M;0,M,mu] =
      -(d • pair 0 1 + M • pair 1 2 + (mu/2) • pair 2 2) := by
  simp [action, Fin.sum_univ_succ]
  rw [pair_symmetric (1 : Fin 3) 0, pair_symmetric (2 : Fin 3) 1]
  simp only [smul_smul]
  module

end
end Physics.WeylGrassmannAction
