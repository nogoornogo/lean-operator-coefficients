import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Tactic

/-!
# The standard `sl₃(ℂ)` simple-root triples

This file realizes the two simple-root `sl₂` triples inside the Lie algebra
of trace-zero three-by-three complex matrices.  It also proves that the six
simple-root generators generate all of `sl₃(ℂ)` as a Lie algebra.  The
remaining two off-diagonal matrix units are obtained as brackets of adjacent
simple-root generators.

This is the concrete algebraic target needed by the `SU(3)` part of the semisimple embedding classification
group-to-Lie and highest-weight bridge.
-/

namespace Math
namespace StandardSl3

open LieAlgebra Set

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The complex Lie algebra of trace-zero three-by-three matrices. -/
abbrev Algebra := LieAlgebra.SpecialLinear.sl (Fin 3) ℂ

private theorem zero_ne_one : (0 : Fin 3) ≠ 1 := by decide
private theorem one_ne_two : (1 : Fin 3) ≠ 2 := by decide
private theorem zero_ne_two : (0 : Fin 3) ≠ 2 := by decide

/-- The first simple coroot `diag(1,-1,0)`. -/
def H1 : Algebra :=
  LieAlgebra.SpecialLinear.singleSubSingle (0 : Fin 3) 1 1

/-- The first simple positive-root vector `E₀₁`. -/
def E1 : Algebra :=
  LieAlgebra.SpecialLinear.single (0 : Fin 3) 1 zero_ne_one 1

/-- The first simple negative-root vector `E₁₀`. -/
def F1 : Algebra :=
  LieAlgebra.SpecialLinear.single (1 : Fin 3) 0 zero_ne_one.symm 1

/-- The second simple coroot `diag(0,1,-1)`. -/
def H2 : Algebra :=
  LieAlgebra.SpecialLinear.singleSubSingle (1 : Fin 3) 2 1

/-- The second simple positive-root vector `E₁₂`. -/
def E2 : Algebra :=
  LieAlgebra.SpecialLinear.single (1 : Fin 3) 2 one_ne_two 1

/-- The second simple negative-root vector `E₂₁`. -/
def F2 : Algebra :=
  LieAlgebra.SpecialLinear.single (2 : Fin 3) 1 one_ne_two.symm 1

/-- The positive composite-root vector `E₀₂`. -/
def E12 : Algebra :=
  LieAlgebra.SpecialLinear.single (0 : Fin 3) 2 zero_ne_two 1

/-- The negative composite-root vector `E₂₀`. -/
def F12 : Algebra :=
  LieAlgebra.SpecialLinear.single (2 : Fin 3) 0 zero_ne_two.symm 1

/-- The first simple-root matrices form an `sl₂` triple. -/
theorem firstIsSl2Triple : IsSl2Triple H1 E1 F1 where
  h_ne_zero := by
    intro hzero
    have hentry := congrArg
      (fun X : Algebra => (X : Matrix (Fin 3) (Fin 3) ℂ) 0 0) hzero
    norm_num [H1] at hentry
  lie_e_f := by
    apply Subtype.ext
    change
      (E1 : Matrix (Fin 3) (Fin 3) ℂ) * (F1 : Matrix (Fin 3) (Fin 3) ℂ) -
          (F1 : Matrix (Fin 3) (Fin 3) ℂ) * (E1 : Matrix (Fin 3) (Fin 3) ℂ) =
        (H1 : Matrix (Fin 3) (Fin 3) ℂ)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E1, F1, H1]
  lie_h_e_nsmul := by
    apply Subtype.ext
    change
      (H1 : Matrix (Fin 3) (Fin 3) ℂ) * (E1 : Matrix (Fin 3) (Fin 3) ℂ) -
          (E1 : Matrix (Fin 3) (Fin 3) ℂ) * (H1 : Matrix (Fin 3) (Fin 3) ℂ) =
        2 • (E1 : Matrix (Fin 3) (Fin 3) ℂ)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E1, H1, Matrix.mul_apply, Fin.sum_univ_three] ; norm_num
  lie_h_f_nsmul := by
    apply Subtype.ext
    change
      (H1 : Matrix (Fin 3) (Fin 3) ℂ) * (F1 : Matrix (Fin 3) (Fin 3) ℂ) -
          (F1 : Matrix (Fin 3) (Fin 3) ℂ) * (H1 : Matrix (Fin 3) (Fin 3) ℂ) =
        -(2 • (F1 : Matrix (Fin 3) (Fin 3) ℂ))
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [F1, H1, Matrix.mul_apply, Fin.sum_univ_three] ; norm_num

/-- The second simple-root matrices form an `sl₂` triple. -/
theorem secondIsSl2Triple : IsSl2Triple H2 E2 F2 where
  h_ne_zero := by
    intro hzero
    have hentry := congrArg
      (fun X : Algebra => (X : Matrix (Fin 3) (Fin 3) ℂ) 1 1) hzero
    simp [H2] at hentry
  lie_e_f := by
    apply Subtype.ext
    change
      (E2 : Matrix (Fin 3) (Fin 3) ℂ) * (F2 : Matrix (Fin 3) (Fin 3) ℂ) -
          (F2 : Matrix (Fin 3) (Fin 3) ℂ) * (E2 : Matrix (Fin 3) (Fin 3) ℂ) =
        (H2 : Matrix (Fin 3) (Fin 3) ℂ)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E2, F2, H2]
  lie_h_e_nsmul := by
    apply Subtype.ext
    change
      (H2 : Matrix (Fin 3) (Fin 3) ℂ) * (E2 : Matrix (Fin 3) (Fin 3) ℂ) -
          (E2 : Matrix (Fin 3) (Fin 3) ℂ) * (H2 : Matrix (Fin 3) (Fin 3) ℂ) =
        2 • (E2 : Matrix (Fin 3) (Fin 3) ℂ)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E2, H2, Matrix.mul_apply, Fin.sum_univ_three] ; norm_num
  lie_h_f_nsmul := by
    apply Subtype.ext
    change
      (H2 : Matrix (Fin 3) (Fin 3) ℂ) * (F2 : Matrix (Fin 3) (Fin 3) ℂ) -
          (F2 : Matrix (Fin 3) (Fin 3) ℂ) * (H2 : Matrix (Fin 3) (Fin 3) ℂ) =
        -(2 • (F2 : Matrix (Fin 3) (Fin 3) ℂ))
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [F2, H2, Matrix.mul_apply, Fin.sum_univ_three] ; norm_num

/-- Bracketing the adjacent positive simple-root vectors produces `E₀₂`. -/
theorem lie_E1_E2 : ⁅E1, E2⁆ = E12 := by
  apply Subtype.ext
  change
    (E1 : Matrix (Fin 3) (Fin 3) ℂ) * (E2 : Matrix (Fin 3) (Fin 3) ℂ) -
        (E2 : Matrix (Fin 3) (Fin 3) ℂ) * (E1 : Matrix (Fin 3) (Fin 3) ℂ) =
      (E12 : Matrix (Fin 3) (Fin 3) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E1, E2, E12]

/-- Bracketing the adjacent negative simple-root vectors in the reverse order
produces `E₂₀`. -/
theorem lie_F2_F1 : ⁅F2, F1⁆ = F12 := by
  apply Subtype.ext
  change
    (F2 : Matrix (Fin 3) (Fin 3) ℂ) * (F1 : Matrix (Fin 3) (Fin 3) ℂ) -
        (F1 : Matrix (Fin 3) (Fin 3) ℂ) * (F2 : Matrix (Fin 3) (Fin 3) ℂ) =
      (F12 : Matrix (Fin 3) (Fin 3) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [F1, F2, F12]

/-- The composite-root vectors form the third canonical `sl₂` triple. -/
theorem compositeIsSl2Triple : IsSl2Triple (H1 + H2) E12 F12 where
  h_ne_zero := by
    intro hzero
    have hentry := congrArg
      (fun X : Algebra => (X : Matrix (Fin 3) (Fin 3) ℂ) 0 0) hzero
    simp [H1, H2, show (2 : Fin 3) ≠ 0 by decide] at hentry
  lie_e_f := by
    apply Subtype.ext
    change
      (E12 : Matrix (Fin 3) (Fin 3) ℂ) * (F12 : Matrix (Fin 3) (Fin 3) ℂ) -
          (F12 : Matrix (Fin 3) (Fin 3) ℂ) * (E12 : Matrix (Fin 3) (Fin 3) ℂ) =
        ((H1 + H2 : Algebra) : Matrix (Fin 3) (Fin 3) ℂ)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E12, F12, H1, H2]
  lie_h_e_nsmul := by
    apply Subtype.ext
    change
      (((H1 + H2 : Algebra) : Matrix (Fin 3) (Fin 3) ℂ) *
          (E12 : Matrix (Fin 3) (Fin 3) ℂ) -
        (E12 : Matrix (Fin 3) (Fin 3) ℂ) *
          ((H1 + H2 : Algebra) : Matrix (Fin 3) (Fin 3) ℂ)) =
        2 • (E12 : Matrix (Fin 3) (Fin 3) ℂ)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E12, H1, H2, Matrix.mul_apply, Fin.sum_univ_three] ; norm_num
  lie_h_f_nsmul := by
    apply Subtype.ext
    change
      (((H1 + H2 : Algebra) : Matrix (Fin 3) (Fin 3) ℂ) *
          (F12 : Matrix (Fin 3) (Fin 3) ℂ) -
        (F12 : Matrix (Fin 3) (Fin 3) ℂ) *
          ((H1 + H2 : Algebra) : Matrix (Fin 3) (Fin 3) ℂ)) =
        -(2 • (F12 : Matrix (Fin 3) (Fin 3) ℂ))
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [F12, H1, H2, Matrix.mul_apply, Fin.sum_univ_three] ; norm_num

/-!
## Cartan and root-vector relations
-/

theorem lie_H2_F1 : ⁅H2, F1⁆ = F1 := by
  apply Subtype.ext
  change
    (H2 : Matrix (Fin 3) (Fin 3) ℂ) * (F1 : Matrix (Fin 3) (Fin 3) ℂ) -
        (F1 : Matrix (Fin 3) (Fin 3) ℂ) * (H2 : Matrix (Fin 3) (Fin 3) ℂ) =
      (F1 : Matrix (Fin 3) (Fin 3) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H2, F1, Matrix.mul_apply, Fin.sum_univ_three]

theorem lie_H1_F2 : ⁅H1, F2⁆ = F2 := by
  apply Subtype.ext
  change
    (H1 : Matrix (Fin 3) (Fin 3) ℂ) * (F2 : Matrix (Fin 3) (Fin 3) ℂ) -
        (F2 : Matrix (Fin 3) (Fin 3) ℂ) * (H1 : Matrix (Fin 3) (Fin 3) ℂ) =
      (F2 : Matrix (Fin 3) (Fin 3) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H1, F2, Matrix.mul_apply, Fin.sum_univ_three]

theorem lie_H1_F12 : ⁅H1, F12⁆ = -F12 := by
  apply Subtype.ext
  change
    (H1 : Matrix (Fin 3) (Fin 3) ℂ) * (F12 : Matrix (Fin 3) (Fin 3) ℂ) -
        (F12 : Matrix (Fin 3) (Fin 3) ℂ) * (H1 : Matrix (Fin 3) (Fin 3) ℂ) =
      -(F12 : Matrix (Fin 3) (Fin 3) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H1, F12, Matrix.mul_apply, Fin.sum_univ_three]

theorem lie_H2_F12 : ⁅H2, F12⁆ = -F12 := by
  apply Subtype.ext
  change
    (H2 : Matrix (Fin 3) (Fin 3) ℂ) * (F12 : Matrix (Fin 3) (Fin 3) ℂ) -
        (F12 : Matrix (Fin 3) (Fin 3) ℂ) * (H2 : Matrix (Fin 3) (Fin 3) ℂ) =
      -(F12 : Matrix (Fin 3) (Fin 3) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H2, F12, Matrix.mul_apply, Fin.sum_univ_three]

theorem lie_E1_F2 : ⁅E1, F2⁆ = 0 := by
  apply Subtype.ext
  change
    (E1 : Matrix (Fin 3) (Fin 3) ℂ) * (F2 : Matrix (Fin 3) (Fin 3) ℂ) -
        (F2 : Matrix (Fin 3) (Fin 3) ℂ) * (E1 : Matrix (Fin 3) (Fin 3) ℂ) = 0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E1, F2]

theorem lie_E2_F1 : ⁅E2, F1⁆ = 0 := by
  apply Subtype.ext
  change
    (E2 : Matrix (Fin 3) (Fin 3) ℂ) * (F1 : Matrix (Fin 3) (Fin 3) ℂ) -
        (F1 : Matrix (Fin 3) (Fin 3) ℂ) * (E2 : Matrix (Fin 3) (Fin 3) ℂ) = 0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E2, F1]

theorem lie_E1_F12 : ⁅E1, F12⁆ = -F2 := by
  apply Subtype.ext
  change
    (E1 : Matrix (Fin 3) (Fin 3) ℂ) * (F12 : Matrix (Fin 3) (Fin 3) ℂ) -
        (F12 : Matrix (Fin 3) (Fin 3) ℂ) * (E1 : Matrix (Fin 3) (Fin 3) ℂ) =
      -(F2 : Matrix (Fin 3) (Fin 3) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E1, F12, F2]

theorem lie_E2_F12 : ⁅E2, F12⁆ = F1 := by
  apply Subtype.ext
  change
    (E2 : Matrix (Fin 3) (Fin 3) ℂ) * (F12 : Matrix (Fin 3) (Fin 3) ℂ) -
        (F12 : Matrix (Fin 3) (Fin 3) ℂ) * (E2 : Matrix (Fin 3) (Fin 3) ℂ) =
      (F1 : Matrix (Fin 3) (Fin 3) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E2, F12, F1]

theorem lie_F1_F12 : ⁅F1, F12⁆ = 0 := by
  apply Subtype.ext
  change
    (F1 : Matrix (Fin 3) (Fin 3) ℂ) * (F12 : Matrix (Fin 3) (Fin 3) ℂ) -
        (F12 : Matrix (Fin 3) (Fin 3) ℂ) * (F1 : Matrix (Fin 3) (Fin 3) ℂ) = 0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [F1, F12]

theorem lie_F2_F12 : ⁅F2, F12⁆ = 0 := by
  apply Subtype.ext
  change
    (F2 : Matrix (Fin 3) (Fin 3) ℂ) * (F12 : Matrix (Fin 3) (Fin 3) ℂ) -
        (F12 : Matrix (Fin 3) (Fin 3) ℂ) * (F2 : Matrix (Fin 3) (Fin 3) ℂ) = 0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [F2, F12]

/-- The six Chevalley generators attached to the two simple roots. -/
def simpleGenerators : Set Algebra := {H1, H2, E1, F1, E2, F2}

private theorem generator_mem_lieSpan (X : Algebra)
    (hX : X ∈ simpleGenerators) :
    X ∈ LieSubalgebra.lieSpan ℂ Algebra simpleGenerators :=
  LieSubalgebra.subset_lieSpan hX

private theorem H1_mem_lieSpan :
    H1 ∈ LieSubalgebra.lieSpan ℂ Algebra simpleGenerators :=
  generator_mem_lieSpan H1 (by simp [simpleGenerators])

private theorem H2_mem_lieSpan :
    H2 ∈ LieSubalgebra.lieSpan ℂ Algebra simpleGenerators :=
  generator_mem_lieSpan H2 (by simp [simpleGenerators])

private theorem E1_mem_lieSpan :
    E1 ∈ LieSubalgebra.lieSpan ℂ Algebra simpleGenerators :=
  generator_mem_lieSpan E1 (by simp [simpleGenerators])

private theorem F1_mem_lieSpan :
    F1 ∈ LieSubalgebra.lieSpan ℂ Algebra simpleGenerators :=
  generator_mem_lieSpan F1 (by simp [simpleGenerators])

private theorem E2_mem_lieSpan :
    E2 ∈ LieSubalgebra.lieSpan ℂ Algebra simpleGenerators :=
  generator_mem_lieSpan E2 (by simp [simpleGenerators])

private theorem F2_mem_lieSpan :
    F2 ∈ LieSubalgebra.lieSpan ℂ Algebra simpleGenerators :=
  generator_mem_lieSpan F2 (by simp [simpleGenerators])

private theorem E12_mem_lieSpan :
    E12 ∈ LieSubalgebra.lieSpan ℂ Algebra simpleGenerators := by
  rw [← lie_E1_E2]
  exact LieSubalgebra.lie_mem _ E1_mem_lieSpan E2_mem_lieSpan

private theorem F12_mem_lieSpan :
    F12 ∈ LieSubalgebra.lieSpan ℂ Algebra simpleGenerators := by
  rw [← lie_F2_F1]
  exact LieSubalgebra.lie_mem _ F2_mem_lieSpan F1_mem_lieSpan

/-- The two simple-root triples generate the full standard `sl₃(ℂ)` Lie
algebra. -/
theorem lieSpan_simpleGenerators_eq_top :
    LieSubalgebra.lieSpan ℂ Algebra simpleGenerators = ⊤ := by
  apply top_unique
  intro X _
  have htrace :
      X.1 0 0 + X.1 1 1 + X.1 2 2 = 0 := by
    have h := X.2
    change Matrix.trace X.1 = 0 at h
    simpa [Matrix.trace_fin_three] using h
  have hdecomp :
      X =
        X.1 0 1 • E1 + X.1 1 0 • F1 +
        X.1 1 2 • E2 + X.1 2 1 • F2 +
        X.1 0 2 • E12 + X.1 2 0 • F12 +
        X.1 0 0 • H1 + (-X.1 2 2) • H2 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E1, F1, E2, F2, E12, F12, H1, H2];
      linear_combination htrace
  rw [hdecomp]
  repeat' apply LieSubalgebra.add_mem
  all_goals
    apply LieSubalgebra.smul_mem
    first
    | exact E1_mem_lieSpan
    | exact F1_mem_lieSpan
    | exact E2_mem_lieSpan
    | exact F2_mem_lieSpan
    | exact E12_mem_lieSpan
    | exact F12_mem_lieSpan
    | exact H1_mem_lieSpan
    | exact H2_mem_lieSpan

/-!
## One-dimensional modules
-/

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable [LieRingModule Algebra V] [LieModule ℂ Algebra V]
variable [FiniteDimensional ℂ V]

/-- Every commutator acts by zero on a one-dimensional complex module because
all endomorphisms of such a module are scalar. -/
theorem bracket_action_eq_zero_of_finrank_eq_one
    (hDimension : Module.finrank ℂ V = 1)
    (X Y : Algebra) (v : V) :
    ⁅⁅X, Y⁆, v⁆ = 0 := by
  obtain ⟨a, ha, _⟩ :=
    (LieModule.toEnd ℂ Algebra V X).existsUnique_eq_smul_id_of_finrank_eq_one
      hDimension
  obtain ⟨b, hb, _⟩ :=
    (LieModule.toEnd ℂ Algebra V Y).existsUnique_eq_smul_id_of_finrank_eq_one
      hDimension
  change (LieModule.toEnd ℂ Algebra V ⁅X, Y⁆) v = 0
  rw [LieHom.map_lie, ha, hb]
  simp

/-- Every action of the concrete standard `sl₃(ℂ)` on a one-dimensional
complex vector space is zero. -/
theorem action_eq_zero_of_finrank_eq_one
    (hDimension : Module.finrank ℂ V = 1)
    (X : Algebra) (v : V) :
    ⁅X, v⁆ = 0 := by
  have hH1 : ⁅H1, v⁆ = 0 := by
    rw [← firstIsSl2Triple.lie_e_f]
    exact bracket_action_eq_zero_of_finrank_eq_one hDimension E1 F1 v
  have hE1 : ⁅E1, v⁆ = 0 := by
    have h := bracket_action_eq_zero_of_finrank_eq_one hDimension H1 E1 v
    rw [firstIsSl2Triple.lie_h_e_smul (R := ℂ), smul_lie] at h
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  have hF1 : ⁅F1, v⁆ = 0 := by
    have h := bracket_action_eq_zero_of_finrank_eq_one hDimension H1 F1 v
    rw [firstIsSl2Triple.lie_lie_smul_f (R := ℂ), neg_lie, smul_lie] at h
    have h' : (2 : ℂ) • ⁅F1, v⁆ = 0 := by simpa using congrArg Neg.neg h
    exact (smul_eq_zero.mp h').resolve_left (by norm_num)
  have hH2 : ⁅H2, v⁆ = 0 := by
    rw [← secondIsSl2Triple.lie_e_f]
    exact bracket_action_eq_zero_of_finrank_eq_one hDimension E2 F2 v
  have hE2 : ⁅E2, v⁆ = 0 := by
    have h := bracket_action_eq_zero_of_finrank_eq_one hDimension H2 E2 v
    rw [secondIsSl2Triple.lie_h_e_smul (R := ℂ), smul_lie] at h
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  have hF2 : ⁅F2, v⁆ = 0 := by
    have h := bracket_action_eq_zero_of_finrank_eq_one hDimension H2 F2 v
    rw [secondIsSl2Triple.lie_lie_smul_f (R := ℂ), neg_lie, smul_lie] at h
    have h' : (2 : ℂ) • ⁅F2, v⁆ = 0 := by simpa using congrArg Neg.neg h
    exact (smul_eq_zero.mp h').resolve_left (by norm_num)
  have hmem : X ∈ LieSubalgebra.lieSpan ℂ Algebra simpleGenerators := by
    rw [lieSpan_simpleGenerators_eq_top]
    exact Set.mem_univ X
  induction hmem using LieSubalgebra.lieSpan_induction with
  | mem Y hY =>
      simp only [simpleGenerators, Set.mem_insert_iff, Set.mem_singleton_iff] at hY
      rcases hY with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hH1
      · exact hH2
      · exact hE1
      · exact hF1
      · exact hE2
      · exact hF2
  | zero => simp
  | add Y Z _ _ hY hZ => simp [hY, hZ]
  | smul c Y _ hY => simp [hY]
  | lie Y Z _ _ hY hZ => simp [hY, hZ]

end

end StandardSl3
end Math
