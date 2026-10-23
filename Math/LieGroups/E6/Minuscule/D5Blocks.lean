import Math.LieGroups.E6.Minuscule.CompactGenerators
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The D5 coordinate blocks of the 27 matrices

Delete E6 node 0, in the pinned Bourbaki numbering. The remaining nodes have
Cartan matrix D5. A commuting integral grading separates 16, 10, and 1
coordinates, and the corresponding coordinate subspaces are invariant.
No identification with irreducible Spin(10) group representations is assumed
or proved here.
-/

set_option autoImplicit false

-- Check finite certificates sequentially to avoid blocked elaboration worker stacks.
set_option Elab.async false

namespace Math.E6.Minuscule

open TauCeti.DynkinType TauCeti.E6Minuscule
open scoped Matrix

/-- D5's chain ends in the two branches numbered 1 and 2 in E6. -/
def d5Node : Fin 5 → Fin 6 := ![5, 4, 3, 1, 2]

theorem d5Node_injective : Function.Injective d5Node := by decide +kernel

theorem d5_cartan (i j : Fin 5) :
    CartanMatrix.E 6 (d5Node i) (d5Node j) = CartanMatrix.D 5 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [CartanMatrix.E, CartanMatrix.D, d5Node]

/-- Three times the first fundamental coweight, in simple-coroot coordinates. -/
def gradingCoefficients : Fin 6 → ℤ := ![4, 3, 5, 6, 4, 2]

def grade (a : Fin 27) : ℤ := ∑ i, gradingCoefficients i * e6MinusculeWeight a i

theorem grading_cartan (j : Fin 6) :
    (∑ i, gradingCoefficients i * CartanMatrix.E 6 i j) =
      if j = 0 then 3 else 0 := by
  decide +kernel +revert

theorem grade_values (a : Fin 27) : grade a = 1 ∨ grade a = -2 ∨ grade a = 4 := by
  decide +kernel +revert

theorem grade_cardinalities :
    (Finset.univ.filter (fun a => grade a = 1)).card = 16 ∧
    (Finset.univ.filter (fun a => grade a = -2)).card = 10 ∧
    (Finset.univ.filter (fun a => grade a = 4)).card = 1 := by
  decide +kernel

theorem grade_four_iff (a : Fin 27) : grade a = 4 ↔ a = 0 := by
  decide +kernel +revert

theorem d5_reflection_preserves_grade (i : Fin 5) (a : Fin 27) :
    grade (e6MinusculeReflection (d5Node i) a) = grade a := by
  decide +kernel +revert

theorem d5_dominant_iff (a : Fin 27) :
    (∀ i : Fin 5, 0 ≤ e6MinusculeWeight a (d5Node i)) ↔ a = 0 ∨ a = 1 ∨ a = 12 := by
  decide +kernel +revert

/-- The three dominant labels are the singlet, one spinor label, and the vector
label. This finite label check is not a highest-weight classification theorem. -/
theorem d5_dominant_labels :
    (fun i => e6MinusculeWeight 0 (d5Node i)) = (0 : Fin 5 → ℤ) ∧
    (fun i => e6MinusculeWeight 1 (d5Node i)) = Pi.single (4 : Fin 5) 1 ∧
    (fun i => e6MinusculeWeight 12 (d5Node i)) = Pi.single (0 : Fin 5) 1 := by
  decide +kernel

theorem d5_dominant_grades : grade 0 = 4 ∧ grade 1 = 1 ∧ grade 12 = -2 := by
  decide +kernel

theorem d5_singlet_annihilated (i : Fin 5) (a : Fin 27) :
    raisingMatrix (d5Node i) a 0 = 0 ∧ loweringMatrix (d5Node i) a 0 = 0 ∧
      cartanGeneratorMatrix (d5Node i) a 0 = 0 := by
  decide +kernel +revert

theorem raisingMatrix_off_block (i : Fin 5) (a b : Fin 27)
    (h : grade a ≠ grade b) : raisingMatrix (d5Node i) a b = 0 := by
  rw [raisingMatrix_apply, ite_eq_right_iff]
  rintro ⟨_, rfl⟩
  exact (h (d5_reflection_preserves_grade i b)).elim

theorem loweringMatrix_off_block (i : Fin 5) (a b : Fin 27)
    (h : grade a ≠ grade b) : loweringMatrix (d5Node i) a b = 0 := by
  rw [loweringMatrix_apply, ite_eq_right_iff]
  rintro ⟨_, rfl⟩
  exact (h (d5_reflection_preserves_grade i b)).elim

noncomputable section

theorem raising_off_block (i : Fin 5) (a b : Fin 27) (h : grade a ≠ grade b) :
    raising (d5Node i) a b = 0 := by
  simp only [raising, TauCeti.matrixIntCastLieHom_apply, raisingMatrix_off_block i a b h,
    Int.cast_zero]

theorem lowering_off_block (i : Fin 5) (a b : Fin 27) (h : grade a ≠ grade b) :
    lowering (d5Node i) a b = 0 := by
  simp only [lowering, TauCeti.matrixIntCastLieHom_apply, loweringMatrix_off_block i a b h,
    Int.cast_zero]

theorem cartan_off_block (i : Fin 6) (a b : Fin 27) (h : grade a ≠ grade b) :
    cartan i a b = 0 := by
  have hab : a ≠ b := fun hab => h (congrArg grade hab)
  simp [cartan, hab]

/-- Actual subspace of the 27-dimensional coordinate space, not a weight count. -/
def gradeSpace (q : ℤ) : Submodule ℂ (Fin 27 → ℂ) where
  carrier := {v | ∀ a, grade a ≠ q → v a = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw a ha
    simp [hv a ha, hw a ha]
  smul_mem' := by
    intro c v hv a ha
    simp [hv a ha]

/-- Restriction to the coordinates of one grade, with extension by zero as inverse. -/
def gradeSpaceEquiv (q : ℤ) : gradeSpace q ≃ₗ[ℂ] ({a : Fin 27 // grade a = q} → ℂ) where
  toFun v a := v.val a.val
  invFun w := ⟨fun a => if h : grade a = q then w ⟨a, h⟩ else 0, by
    intro a ha
    simp [ha]⟩
  left_inv v := by
    apply Subtype.ext
    funext a
    by_cases ha : grade a = q
    · simp [ha]
    · simp [ha, v.property a ha]
  right_inv w := by
    funext a
    simp [a.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem gradeSpace_finrank (q : ℤ) :
    Module.finrank ℂ (gradeSpace q) = (Finset.univ.filter (fun a => grade a = q)).card := by
  rw [(gradeSpaceEquiv q).finrank_eq, Module.finrank_pi]
  exact Fintype.card_subtype _

theorem gradeSpace_dimensions :
    Module.finrank ℂ (gradeSpace 1) = 16 ∧
    Module.finrank ℂ (gradeSpace (-2)) = 10 ∧
    Module.finrank ℂ (gradeSpace 4) = 1 := by
  simpa only [gradeSpace_finrank] using grade_cardinalities

def gradeProjection (q : ℤ) (v : Fin 27 → ℂ) : Fin 27 → ℂ :=
  fun a => if grade a = q then v a else 0

theorem gradeProjection_mem (q : ℤ) (v : Fin 27 → ℂ) :
    gradeProjection q v ∈ gradeSpace q := by
  intro a ha
  simp [gradeProjection, ha]

theorem grade_decomposition (v : Fin 27 → ℂ) :
    v = gradeProjection 1 v + gradeProjection (-2) v + gradeProjection 4 v := by
  funext a
  rcases grade_values a with h | h | h <;> simp [gradeProjection, h]

theorem gradeSpace_intersection {q r : ℤ} (hqr : q ≠ r) (v : Fin 27 → ℂ)
    (hq : v ∈ gradeSpace q) (hr : v ∈ gradeSpace r) : v = 0 := by
  funext a
  by_cases h : grade a = q
  · exact hr a (by simpa [h] using hqr)
  · exact hq a h

theorem mulVec_mem_gradeSpace (M : Matrix27)
    (hM : ∀ a b, grade a ≠ grade b → M a b = 0)
    (q : ℤ) (v : Fin 27 → ℂ) (hv : v ∈ gradeSpace q) :
    M *ᵥ v ∈ gradeSpace q := by
  intro a ha
  change ∑ b, M a b * v b = 0
  apply Finset.sum_eq_zero
  intro b _
  by_cases hb : grade b = q
  · have hab : grade a ≠ grade b := fun h => ha (h.trans hb)
    simp [hM a b hab]
  · simp [hv b hb]

theorem d5_generators_preserve_gradeSpace (i : Fin 5) (q : ℤ)
    (v : Fin 27 → ℂ) (hv : v ∈ gradeSpace q) :
    raising (d5Node i) *ᵥ v ∈ gradeSpace q ∧
    lowering (d5Node i) *ᵥ v ∈ gradeSpace q ∧
    cartan (d5Node i) *ᵥ v ∈ gradeSpace q :=
  ⟨mulVec_mem_gradeSpace _ (raising_off_block i) q v hv,
   mulVec_mem_gradeSpace _ (lowering_off_block i) q v hv,
   mulVec_mem_gradeSpace _ (cartan_off_block (d5Node i)) q v hv⟩

end

end Math.E6.Minuscule
