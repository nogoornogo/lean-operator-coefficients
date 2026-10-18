import Math.Algebra.Lie.Sl2String
import Mathlib.Algebra.Lie.Classical
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Tactic

/-!
# The standard `sl₂(ℂ)` triple

This file realizes the abstract `sl₂` triple used by `Sl2String` inside the
Lie algebra of trace-zero two-by-two complex matrices.  It proves directly
that the standard matrices `H`, `E`, and `F` satisfy the `sl₂` relations and
span the whole Lie algebra.
-/

namespace Math
namespace StandardSl2

open LieAlgebra

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The complex Lie algebra of trace-zero two-by-two matrices. -/
abbrev Algebra := LieAlgebra.SpecialLinear.sl (Fin 2) ℂ

private theorem zero_ne_one : (0 : Fin 2) ≠ 1 := by decide

/-- The standard Cartan generator `diag(1,-1)`. -/
def H : Algebra :=
  LieAlgebra.SpecialLinear.singleSubSingle (0 : Fin 2) 1 1

/-- The standard raising matrix. -/
def E : Algebra :=
  LieAlgebra.SpecialLinear.single (0 : Fin 2) 1 zero_ne_one 1

/-- The standard lowering matrix. -/
def F : Algebra :=
  LieAlgebra.SpecialLinear.single (1 : Fin 2) 0 zero_ne_one.symm 1

/-- The standard matrices form an `sl₂` triple. -/
theorem isSl2Triple : IsSl2Triple H E F where
  h_ne_zero := by
    intro hzero
    have hentry := congrArg (fun X : Algebra => (X : Matrix (Fin 2) (Fin 2) ℂ) 0 0) hzero
    norm_num [H] at hentry
  lie_e_f := by
    apply Subtype.ext
    change
      (E : Matrix (Fin 2) (Fin 2) ℂ) * (F : Matrix (Fin 2) (Fin 2) ℂ) -
          (F : Matrix (Fin 2) (Fin 2) ℂ) * (E : Matrix (Fin 2) (Fin 2) ℂ) =
        (H : Matrix (Fin 2) (Fin 2) ℂ)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E, F, H]
  lie_h_e_nsmul := by
    apply Subtype.ext
    change
      (H : Matrix (Fin 2) (Fin 2) ℂ) * (E : Matrix (Fin 2) (Fin 2) ℂ) -
          (E : Matrix (Fin 2) (Fin 2) ℂ) * (H : Matrix (Fin 2) (Fin 2) ℂ) =
        2 • (E : Matrix (Fin 2) (Fin 2) ℂ)
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [E, H, Matrix.mul_apply, Fin.sum_univ_two]
  lie_h_f_nsmul := by
    apply Subtype.ext
    change
      (H : Matrix (Fin 2) (Fin 2) ℂ) * (F : Matrix (Fin 2) (Fin 2) ℂ) -
          (F : Matrix (Fin 2) (Fin 2) ℂ) * (H : Matrix (Fin 2) (Fin 2) ℂ) =
        -(2 • (F : Matrix (Fin 2) (Fin 2) ℂ))
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [F, H, Matrix.mul_apply, Fin.sum_univ_two]

/-- Every trace-zero two-by-two matrix is a linear combination of `E`, `F`,
and `H`; equivalently, the standard triple spans `sl₂(ℂ)`. -/
theorem toLieSubalgebra_eq_top :
    isSl2Triple.toLieSubalgebra ℂ = ⊤ := by
  apply top_unique
  intro X _
  rw [IsSl2Triple.mem_toLieSubalgebra_iff]
  refine ⟨X.1 0 1, X.1 1 0, X.1 0 0, ?_⟩
  have htrace : X.1 0 0 + X.1 1 1 = 0 := by
    simpa [LieAlgebra.SpecialLinear.sl, Matrix.trace_fin_two] using X.2
  rw [isSl2Triple.lie_e_f]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simp [E, F, H]
  · simp [E, F, H]
  · simp [E, F, H]
  · simpa [E, F, H] using eq_neg_of_add_eq_zero_right htrace

/-!
## One-dimensional modules
-/

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable [LieRingModule Algebra V] [LieModule ℂ Algebra V]
variable [FiniteDimensional ℂ V]

/-- In a one-dimensional module, every commutator in the acting Lie algebra
acts by zero.  Indeed, all endomorphisms of a one-dimensional complex vector
space are scalar and hence commute. -/
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

/-- Every action of `sl₂(ℂ)` on a one-dimensional complex vector space is
zero.  The proof uses the checked spanning triple: `H = [E,F]`, while `E`
and `F` are scalar multiples of `[H,E]` and `[H,F]`. -/
theorem action_eq_zero_of_finrank_eq_one
    (hDimension : Module.finrank ℂ V = 1)
    (X : Algebra) (v : V) :
    ⁅X, v⁆ = 0 := by
  have hH : ⁅H, v⁆ = 0 := by
    rw [← isSl2Triple.lie_e_f]
    exact bracket_action_eq_zero_of_finrank_eq_one hDimension E F v
  have hE : ⁅E, v⁆ = 0 := by
    have h := bracket_action_eq_zero_of_finrank_eq_one hDimension H E v
    rw [isSl2Triple.lie_h_e_smul (R := ℂ), smul_lie] at h
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  have hF : ⁅F, v⁆ = 0 := by
    have h := bracket_action_eq_zero_of_finrank_eq_one hDimension H F v
    rw [isSl2Triple.lie_lie_smul_f (R := ℂ), neg_lie, smul_lie] at h
    have h' : (2 : ℂ) • ⁅F, v⁆ = 0 := by simpa using congrArg Neg.neg h
    exact (smul_eq_zero.mp h').resolve_left (by norm_num)
  have hmem : X ∈ isSl2Triple.toLieSubalgebra ℂ := by
    rw [toLieSubalgebra_eq_top]
    exact Set.mem_univ X
  obtain ⟨a, b, c, hX⟩ :=
    (IsSl2Triple.mem_toLieSubalgebra_iff (R := ℂ)).mp hmem
  rw [hX, add_lie, add_lie, smul_lie, smul_lie, smul_lie,
    isSl2Triple.lie_e_f, hE, hF, hH]
  simp

end

end StandardSl2
end Math
