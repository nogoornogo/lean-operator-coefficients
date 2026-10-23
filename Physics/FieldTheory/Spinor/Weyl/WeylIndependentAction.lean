import Physics.FieldTheory.Spinor.Weyl.WeylRealTransvections
import Math.RepresentationTheory.Invariants.PairedPolynomialInvariants

/-! Independent complex left/right factors and their actual real-form embedding. -/
namespace Physics.WeylIndependentAction
set_option autoImplicit false
noncomputable section
open Math Representation
abbrev Group := WeylSpinor.Group × WeylSpinor.Group

def paired : WeylSpinor.Group →* Group :=
  PairedPolynomialInvariants.paired WeylSpinor.conjugate

def spin (right : Bool) : Representation ℂ Group WeylSpinor.Space :=
  if right then WeylSpinor.left.comp (MonoidHom.snd _ _) else WeylSpinor.left.comp (MonoidHom.fst _ _)

theorem spin_paired (right : Bool) : (spin right).comp paired = FourSameWeylCompleteness.action right := by
  cases right <;> rfl

def family (a : WeylRealTransvections.Pair) (z : ℂ) : WeylSpinor.Group :=
  Matrix.SpecialLinearGroup.transvection a.property z

theorem family_zero (a : WeylRealTransvections.Pair) : family a 0 = 1 := by
  apply Subtype.ext
  simp [family,Matrix.SpecialLinearGroup.transvection]

theorem family_conjugate (a : WeylRealTransvections.Pair) (z : ℂ) :
    WeylSpinor.conjugate (family a z) = family a (star z) := by
  apply Subtype.ext
  ext i j
  change star ((1 + Matrix.single a.val.1 a.val.2 z : Matrix (Fin 2) (Fin 2) ℂ) i j) =
    (1 + Matrix.single a.val.1 a.val.2 (star z) : Matrix (Fin 2) (Fin 2) ℂ) i j
  simp only [Matrix.add_apply,Matrix.one_apply,Matrix.single_apply]
  split_ifs <;> simp

theorem family_generates : Subgroup.closure
    (Set.range (fun az : WeylRealTransvections.Pair × ℂ => family az.1 az.2)) = ⊤ := by
  apply top_unique
  rw [← WeylGeneratorTests.generates]
  apply Subgroup.closure_mono
  rintro _ ⟨a,rfl⟩
  exact ⟨(⟨(a.i,a.j),a.hij⟩,a.c),rfl⟩

def direction (a : WeylRealTransvections.Pair) : Module.End ℂ WeylSpinor.Space :=
  Matrix.toLin' (Matrix.single a.val.1 a.val.2 1)

theorem spin_affine (right : Bool) (a : WeylRealTransvections.Pair) (u v : ℂ) (x : WeylSpinor.Space) :
    spin right (family a u,family a v) x = x + (if right then v else u) • direction a x := by
  have hh (z : ℂ) : WeylSpinor.left (family a z) x = x + z • direction a x := by
    rcases a with ⟨⟨i,j⟩,hij⟩
    fin_cases i <;> fin_cases j <;> try contradiction
    all_goals ext k; fin_cases k <;>
      simp [family,direction,WeylSpinor.left,Matrix.SpecialLinearGroup.transvection,
        Matrix.transvection,Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Matrix.single_apply]
  cases right <;> exact hh _

end
end Physics.WeylIndependentAction
