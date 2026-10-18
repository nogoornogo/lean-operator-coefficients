import Physics.FieldTheory.Spinor.WeylGeneratorTests
import Physics.FieldTheory.Spinor.FourSameWeylCompleteness
import Math.RepresentationTheory.AffineStatisticalSampling

/-! Four actual real-parameter transvection families preserve paired Weyl actions. -/
namespace GUT.WeylRealTransvections
set_option autoImplicit false
noncomputable section
open Math Representation
abbrev Pair := {ij : Fin 2 × Fin 2 // ij.1 ≠ ij.2}
abbrev Index := Pair × Bool

theorem card_index : Fintype.card Index = 4 := by decide

def phase (imaginary : Bool) : ℂ := if imaginary then Complex.I else 1
def family (a : Index) (t : ℝ) : WeylSpinor.Group :=
  Matrix.SpecialLinearGroup.transvection a.1.property (phase a.2 * (t : ℂ))

theorem split_transvection (t : WeylGeneratorTests.Index) :
    WeylGeneratorTests.generator t =
      family (⟨(t.i,t.j),t.hij⟩, false) t.c.re *
      family (⟨(t.i,t.j),t.hij⟩, true) t.c.im := by
  apply Subtype.ext
  change Matrix.transvection t.i t.j t.c =
    Matrix.transvection t.i t.j (phase false * (t.c.re : ℂ)) *
    Matrix.transvection t.i t.j (phase true * (t.c.im : ℂ))
  rw [Matrix.transvection_mul_transvection_same (i := t.i) (j := t.j) t.hij
    (phase false * (t.c.re : ℂ)) (phase true * (t.c.im : ℂ))]
  simp only [phase, Bool.false_eq_true, ↓reduceIte, one_mul]
  congr 1
  apply Complex.ext <;> simp

theorem generates :
    Subgroup.closure (Set.range (fun ax : Index × ℝ => family ax.1 ax.2)) = ⊤ := by
  have he : Set.range WeylGeneratorTests.generator ⊆
      Subgroup.closure (Set.range (fun ax : Index × ℝ => family ax.1 ax.2)) := by
    rintro _ ⟨t,rfl⟩
    rw [split_transvection]
    apply Subgroup.mul_mem
    · exact Subgroup.subset_closure ⟨(_,t.c.re),rfl⟩
    · exact Subgroup.subset_closure ⟨(_,t.c.im),rfl⟩
  apply top_unique
  rw [← WeylGeneratorTests.generates]
  exact (Subgroup.closure_le _).mpr he

/-- The affine coefficient for the actual left or conjugate-right action. -/
def direction (rightHanded : Bool) (a : Index) : Module.End ℂ WeylSpinor.Space :=
  Matrix.toLin' (Matrix.single a.1.val.1 a.1.val.2
    (if rightHanded then star (phase a.2) else phase a.2))

theorem spinor_affine (rightHanded : Bool) (a : Index) (t : ℝ) (v : WeylSpinor.Space) :
    FourSameWeylCompleteness.action rightHanded (family a t) v =
      v + (t : ℂ) • direction rightHanded a v := by
  have hact : FourSameWeylCompleteness.action rightHanded (family a t) v =
      (if rightHanded then (family a t).val.map star else (family a t).val).mulVec v := by
    cases rightHanded <;> rfl
  rw [hact]
  rcases a with ⟨⟨⟨i,j⟩,hij⟩,imaginary⟩
  cases rightHanded <;> cases imaginary <;> fin_cases i <;> fin_cases j <;>
    try contradiction
  all_goals
    ext k
    fin_cases k <;>
      simp [family, phase, direction, Matrix.SpecialLinearGroup.transvection,
        Matrix.transvection, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Matrix.single_apply, mul_comm] <;> ring


def tests (D : ℕ) (ai : Index × Fin (D+1)) : WeylSpinor.Group :=
  family ai.1 (AffineStatisticalSampling.samples D ai.2)

theorem card_tests (D : ℕ) : Fintype.card (Index × Fin (D+1)) = 4*(D+1) := by
  rw [Fintype.card_prod, card_index, Fintype.card_fin]

theorem exhaustive {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ WeylSpinor.Group V) (D : ℕ)
    (hp : ∀ a, AffineStatisticalSampling.PolynomialOrbits (family a) rho D) :
    FiniteInvariantKernel.Exhaustive rho (tests D) := by
  intro f hf
  apply (GeneratorInvariantTests.invariant_iff rho _ generates f).mpr
  intro ax x
  exact AffineStatisticalSampling.family_invariant (family ax.1) rho D (hp ax.1) f
    (fun i => hf (ax.1,i)) ax.2 x

end
end GUT.WeylRealTransvections
