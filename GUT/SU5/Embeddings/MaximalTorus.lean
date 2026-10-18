import GUT.SU5.Representations.MonomialElements
import Math.LieGroups.SpecialUnitary.RankFive.DeterminantOneTorus

open Math

/-!
# Determinant-one diagonal torus and actual Weyl conjugation

The torus retains all five circle coordinates with their product constraint.
Permutation matrices are corrected to lie in SU(5); their conjugation action
really permutes the diagonal entries. No character model is assumed here.
-/

set_option autoImplicit false
open scoped BigOperators

namespace GUT.SU5.MaximalTorus

open Math.SU5.MaximalTorus
noncomputable section

open StandardModelEmbedding MonomialElements

def hom : Torus →* TargetGroup where
  toFun z := diagonalElement z.val z.property
  map_one' := by apply Subtype.ext; exact Matrix.diagonal_one
  map_mul' z w := by
    apply Subtype.ext
    exact (Matrix.diagonal_mul_diagonal _ _).symm

theorem hom_injective : Function.Injective hom := by
  intro z w he
  apply Subtype.ext
  funext i
  apply Circle.coe_injective
  have hh := congrArg (fun g : TargetGroup => (g : Matrix (Fin 5) (Fin 5) ℂ) i i) he
  simpa [hom, diagonalElement] using hh

theorem hom_permutes (p : Equiv.Perm (Fin 5)) (z : Torus) :
    hom (permute p z) * signedPermutation p = signedPermutation p * hom z := by
  apply Subtype.ext
  have he : Matrix.diagonal (fun i => (z.val (p i) : ℂ)) * p.permMatrix ℂ =
      p.permMatrix ℂ * Matrix.diagonal (fun i => (z.val i : ℂ)) := by
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases h : p i = j
    · subst j; simp [mul_comm]
    · simp [Equiv.Perm.permMatrix, Equiv.toPEquiv_apply, h]
  change Matrix.diagonal (fun i => (z.val (p i) : ℂ)) *
      (signedPermutation p : Matrix (Fin 5) (Fin 5) ℂ) =
    (signedPermutation p : Matrix (Fin 5) (Fin 5) ℂ) *
      Matrix.diagonal (fun i => (z.val i : ℂ))
  by_cases hp : Equiv.Perm.sign p = 1
  · simpa only [signedPermutation, dite_eq_left hp] using he
  · simpa only [signedPermutation, dite_eq_right hp, mul_neg, neg_mul] using congrArg Neg.neg he

theorem hom_conjugate (p : Equiv.Perm (Fin 5)) (z : Torus) :
    hom (permute p z) = signedPermutation p * hom z * (signedPermutation p)⁻¹ := by
  rw [← hom_permutes, mul_inv_cancel_right]

end

end GUT.SU5.MaximalTorus
