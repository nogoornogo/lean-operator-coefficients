import GUT.SUN.Matching.ConjugatedMatching
import GUT.SUN.Matching.Controls

open Math

/-! Identity, composition and specialization controls for simultaneous transport. -/
set_option autoImplicit false
namespace GUT.SUN.ConjugatedControls

noncomputable section
open ConjugatedMatter ExteriorSquareTransport DiagonalBackground
variable {r : ℕ}

theorem rotation_one : rotation (1 : ExteriorMatter.Group r) = LinearEquiv.refl ℂ _ := by
  apply LinearEquiv.ext
  intro x
  change ExteriorMatter.fundamental r 1 x = x
  rw [map_one]
  rfl

theorem rotation_mul (U V : ExteriorMatter.Group r) :
    (rotation V).trans (rotation U) = rotation (U*V) := by
  apply LinearEquiv.ext
  intro x
  change (ExteriorMatter.fundamental r U * ExteriorMatter.fundamental r V) x =
    ExteriorMatter.fundamental r (U*V) x
  rw [map_mul]

theorem background_one (D : Background r) : background 1 D = D.matrix := by
  rw [background, rotation_one, conjugate_refl]
theorem background_mul (U V : ExteriorMatter.Group r) (D : Background r) :
    background (U*V) D = conjugate (rotation U) (background V D) := by
  rw [background, background, conjugate_trans, rotation_mul]

theorem inclusion_one :
    ConjugatedMatter.inclusion (1 : ExteriorMatter.Group r) = ExteriorMatter.inclusion r := by
  ext g
  simp [ConjugatedMatter.inclusion]
theorem inclusion_mul (U V : ExteriorMatter.Group r) :
    (MulAut.conj U).toMonoidHom.comp (ConjugatedMatter.inclusion V) =
      ConjugatedMatter.inclusion (U*V) := by
  ext g
  simp [ConjugatedMatter.inclusion, MulAut.conj_apply, mul_assoc]

theorem identity_generated (D : Background r) (g : ℝ) (hg : g ≠ 0) :
    ConjugatedMatching.generated 1 D (LinearEquiv.refl ℂ _) g hg =
      TreeMatching.generated D g hg :=
  ConjugatedMatching.generated_eq _ _ _ _ _

theorem su7_generated (U : ExteriorMatter.Group 2) (t g : ℝ) (hg : g ≠ 0) :
    ConjugatedMatching.generated U (MatchingControls.su7 t) (LinearEquiv.refl ℂ _) g hg =
      SU5.MediatorMatching.generated g 1 hg one_ne_zero := by
  rw [ConjugatedMatching.generated_eq, MatchingControls.su7_generated]

end
end GUT.SUN.ConjugatedControls
