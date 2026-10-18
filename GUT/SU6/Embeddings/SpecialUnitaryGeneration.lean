import GUT.SU6.Embeddings.SpecialUnitaryLieAlgebra
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

open Math

/-!
# Generation of finite special unitary groups by compact exponentials

For finite matrices the spectrum is finite, so the principal argument is
continuous on the spectrum even when `-1` occurs.  Continuous functional
calculus therefore gives a self-adjoint logarithm for every unitary matrix.

For a special unitary matrix, subtracting the mean trace makes this logarithm
traceless.  A second traceless diagonal logarithm corrects the resulting
scalar phase.  Consequently every element of `SU(N)`, for `N > 0`, is a
product of two exponentials from the compact real form.  This is precisely
the finite-product generation fact needed by the semisimple embedding classification integration bridge; no
surjectivity theorem for one exponential is required.
-/

namespace GUT
namespace SpecialUnitaryGeneration

noncomputable section

open Complex NormedSpace selfAdjoint Unitary
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every finite complex unitary matrix is the exponential of the principal
self-adjoint argument.  This extends the local CFC result to spectra that may
contain `-1`; finiteness makes the argument continuous on the spectrum. -/
lemma expUnitary_argSelfAdjoint_matrix (u : Matrix.unitaryGroup n ℂ) :
    expUnitary (argSelfAdjoint u) = u := by
  apply Subtype.ext
  have hContinuous : ContinuousOn arg
      (spectrum ℂ (u : Matrix n n ℂ)) :=
    (Matrix.finite_spectrum (u : Matrix n n ℂ)).continuousOn _
  rw [expUnitary_coe, argSelfAdjoint_coe,
    ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← cfc_comp_smul ..,
    ← cfc_comp' ..]
  conv_rhs => rw [← cfc_id' ℂ (u : Matrix n n ℂ)]
  refine cfc_congr fun y hy ↦ ?_
  have hyNorm : ‖y‖ = 1 := spectrum.norm_eq_one_of_unitary u.2 hy
  have hLog : I * y.arg = log y :=
    Complex.ext (by simp [log_re, hyNorm]) (by simp [log_im])
  simpa [← exp_eq_exp_ℂ, hLog] using exp_log (by aesop)

variable {N : ℕ}

/-- Forget the determinant-one condition. -/
def unitaryPart (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Matrix.unitaryGroup (Fin N) ℂ :=
  ⟨U.1, U.2.1⟩

/-- The principal self-adjoint logarithm of a special unitary matrix. -/
def logarithm (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    selfAdjoint (Matrix (Fin N) (Fin N) ℂ) :=
  argSelfAdjoint (unitaryPart U)

lemma exp_I_smul_logarithm
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    exp (I • (logarithm U : Matrix (Fin N) (Fin N) ℂ)) = U := by
  exact congr_arg Subtype.val
    (expUnitary_argSelfAdjoint_matrix (unitaryPart U))

lemma trace_logarithm_star_eq
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    star (Matrix.trace (logarithm U : Matrix (Fin N) (Fin N) ℂ)) =
      Matrix.trace (logarithm U : Matrix (Fin N) (Fin N) ℂ) := by
  rw [← Matrix.trace_conjTranspose]
  rw [← Matrix.star_eq_conjTranspose]
  rw [(logarithm U).2.star_eq]

/-- The determinant-one condition says that the exponential of `i` times the
trace of the principal logarithm is one. -/
lemma exp_I_mul_trace_logarithm
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Complex.exp
        (I * Matrix.trace (logarithm U : Matrix (Fin N) (Fin N) ℂ)) = 1 := by
  have hDet := congr_arg Matrix.det (exp_I_smul_logarithm U)
  rw [MatrixDeterminantExponential.det_exp] at hDet
  simpa using hDet.trans U.2.2

def traceMean (U : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℂ :=
  Matrix.trace (logarithm U : Matrix (Fin N) (Fin N) ℂ) / N

def centeredLog (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (logarithm U : Matrix (Fin N) (Fin N) ℂ) - traceMean U • 1

lemma trace_centeredLog
    [NeZero N]
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Matrix.trace (centeredLog U) = 0 := by
  simp only [centeredLog, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_one, smul_eq_mul, traceMean, Fintype.card_fin]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  field_simp [hN]
  ring

lemma traceMean_star_eq
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    star (traceMean U) = traceMean U := by
  simp only [traceMean, star_div₀, star_natCast]
  rw [trace_logarithm_star_eq]

lemma centeredLog_isSelfAdjoint
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    IsSelfAdjoint (centeredLog U) := by
  exact (logarithm U).2.sub
    ((Matrix.isHermitian_one (n := Fin N)).smul (traceMean_star_eq U))

/-- Exponentiating the centered logarithm differs from the original special
unitary matrix only by a scalar phase. -/
lemma exp_centeredLog
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    exp (I • centeredLog U) =
      (U : Matrix (Fin N) (Fin N) ℂ) *
        (Complex.exp (-(I * traceMean U)) •
          (1 : Matrix (Fin N) (Fin N) ℂ)) := by
  have hExpScalar (z : ℂ) :
      exp (z • (1 : Matrix (Fin N) (Fin N) ℂ)) =
        Complex.exp z • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one, ← exp_eq_exp_ℂ] using
      (algebraMap_exp_comm
        (𝕂 := ℂ) (𝔸 := Matrix (Fin N) (Fin N) ℂ) z).symm
  have hCentered :
      I • centeredLog U =
        I • (logarithm U : Matrix (Fin N) (Fin N) ℂ) +
          (-(I * traceMean U)) •
            (1 : Matrix (Fin N) (Fin N) ℂ) := by
    ext i j
    simp only [centeredLog, smul_sub, neg_smul]
    by_cases hij : i = j
    · subst j
      simp
      ring
    · simp [hij]
  have hCommute : Commute
      (I • (logarithm U : Matrix (Fin N) (Fin N) ℂ))
      ((-(I * traceMean U)) •
        (1 : Matrix (Fin N) (Fin N) ℂ)) := by
    rw [Commute, SemiconjBy]
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (Algebra.commutes (-(I * traceMean U))
        (I • (logarithm U : Matrix (Fin N) (Fin N) ℂ))).symm
  rw [hCentered]
  rw [Matrix.exp_add_of_commute _ _ hCommute]
  rw [exp_I_smul_logarithm, hExpScalar]

/-- The centered logarithm, multiplied by `i`, as an element of `su(N)`. -/
def centeredLogParameter
    [NeZero N]
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    SpecialUnitaryLieAlgebra.CompactRealForm (Fin N) where
  toSpecialLinear :=
    ⟨I • centeredLog U, by
      change Matrix.trace (I • centeredLog U) = 0
      rw [Matrix.trace_smul, trace_centeredLog, smul_zero]⟩
  skewAdjoint := (centeredLog_isSelfAdjoint U).I_smul_mem_skewAdjoint

/-- A diagonal skew-adjoint correction.  One distinguished diagonal entry
uses the determinant-one relation to keep the correction traceless without
changing its exponential. -/
def correctionEntry
    [NeZero N]
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) (j : Fin N) : ℂ :=
  I * traceMean U -
    if j = 0 then
      I * Matrix.trace (logarithm U : Matrix (Fin N) (Fin N) ℂ)
    else 0

def correctionMatrix
    [NeZero N]
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (correctionEntry U)

lemma trace_correctionMatrix
    [NeZero N]
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Matrix.trace (correctionMatrix U) = 0 := by
  simp only [correctionMatrix, Matrix.trace_diagonal, correctionEntry,
    Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_eq_left]
  simp only [traceMean]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  field_simp [hN]
  ring

lemma correctionEntry_star_eq_neg
    [NeZero N]
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) (j : Fin N) :
    star (correctionEntry U j) = -correctionEntry U j := by
  simp only [correctionEntry, star_sub, star_mul, traceMean_star_eq,
    trace_logarithm_star_eq, apply_ite, star_zero]
  rw [show star (I : ℂ) = -I from Complex.conj_I]
  split_ifs <;> ring

lemma correctionMatrix_mem_skewAdjoint
    [NeZero N]
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    correctionMatrix U ∈ skewAdjoint (Matrix (Fin N) (Fin N) ℂ) := by
  rw [skewAdjoint.mem_iff]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [correctionMatrix, correctionEntry_star_eq_neg]
  · simp [correctionMatrix, hij, Ne.symm hij]

def correctionParameter
    [NeZero N]
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    SpecialUnitaryLieAlgebra.CompactRealForm (Fin N) where
  toSpecialLinear :=
    ⟨correctionMatrix U, by
      change Matrix.trace (correctionMatrix U) = 0
      exact trace_correctionMatrix U⟩
  skewAdjoint := correctionMatrix_mem_skewAdjoint U

lemma exp_correctionEntry
    [NeZero N]
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) (j : Fin N) :
    Complex.exp (correctionEntry U j) =
      Complex.exp (I * traceMean U) := by
  by_cases hj : j = 0
  · simp only [correctionEntry, hj, ite_eq_left]
    rw [Complex.exp_sub, exp_I_mul_trace_logarithm]
    simp
  · simp [correctionEntry, hj]

lemma exp_correctionMatrix
    [NeZero N]
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    exp (correctionMatrix U) =
      Complex.exp (I * traceMean U) •
        (1 : Matrix (Fin N) (Fin N) ℂ) := by
  rw [correctionMatrix, Matrix.exp_diagonal]
  rw [show (NormedSpace.exp (correctionEntry U)) =
      fun _ ↦ Complex.exp (I * traceMean U) by
    ext j
    rw [Pi.coe_exp]
    simpa only [← exp_eq_exp_ℂ] using exp_correctionEntry U j]
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- The two explicitly constructed compact-real-form exponentials multiply
to the original special unitary matrix. -/
lemma expSpecialUnitary_centered_mul_correction
    [NeZero N]
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    SpecialUnitaryLieAlgebra.CompactRealForm.expSpecialUnitary
        (centeredLogParameter U) *
      SpecialUnitaryLieAlgebra.CompactRealForm.expSpecialUnitary
        (correctionParameter U) = U := by
  apply Subtype.ext
  change exp (I • centeredLog U) * exp (correctionMatrix U) = U
  rw [exp_centeredLog, exp_correctionMatrix]
  rw [← Algebra.algebraMap_eq_smul_one,
    ← Algebra.algebraMap_eq_smul_one]
  rw [Matrix.mul_assoc, ← map_mul, ← Complex.exp_add]
  simp

/-- Every `SU(N)` element, for `N > 0`, is a product of two exponentials from
the concrete compact real form. -/
def compactExponentialGeneration [NeZero N] :
    ExponentialRepresentationBridge.FiniteProductGeneration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
      (SpecialUnitaryLieAlgebra.CompactRealForm (Fin N)) where
  generator :=
    SpecialUnitaryLieAlgebra.CompactRealForm.expSpecialUnitary
  generates U := by
    refine ⟨[centeredLogParameter U, correctionParameter U], ?_⟩
    simpa using expSpecialUnitary_centered_mul_correction U

end

end SpecialUnitaryGeneration

namespace SpecialUnitaryLieAlgebra

open CompactEmbeddingClassification ExponentialRepresentationBridge
  HighestWeightBridge

noncomputable section

universe v

/-!
## Representation-model constructors

The group-dependent generation input is now supplied by
`SpecialUnitaryGeneration.compactExponentialGeneration`.  The only remaining
input in these constructors is compatibility of the represented action with
the differentiated action on compact exponentials.
-/

/-- Construct the generated `SU(2)` Lie model without assuming that every
group element is one exponential. -/
def su2GeneratedModelOfCompactGeneration
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ SU2 V)
    [FiniteDimensional ℂ V]
    [LieRingModule StandardSl2.Algebra V]
    [LieModule ℂ StandardSl2.Algebra V]
    (hAction : ∀ X : CompactRealForm (Fin 2),
      rho (CompactRealForm.expSpecialUnitary X) =
        finiteDimensionalExponential
          (LieModule.toEnd ℂ StandardSl2.Algebra V X.toSpecialLinear)) :
    SU2GeneratedExponentialStandardLieModel rho where
  finiteDimensional := inferInstance
  lieRingModule := inferInstance
  lieModule := inferInstance
  parameter := CompactRealForm (Fin 2)
  generation :=
    SpecialUnitaryGeneration.compactExponentialGeneration (N := 2)
  toComplexLie := CompactRealForm.toSpecialLinear
  action_generator := hAction
  centerParameter := su2CenterParameter
  center_generator := expSpecialUnitary_su2CenterParameter
  center_lie := rfl

/-- Construct the analogous generated `SU(3)` Lie model. -/
def su3ModelOfCompactGeneration
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ SU3 V)
    [FiniteDimensional ℂ V]
    [LieRingModule StandardSl3.Algebra V]
    [LieModule ℂ StandardSl3.Algebra V]
    (hAction : ∀ X : CompactRealForm (Fin 3),
      rho (CompactRealForm.expSpecialUnitary X) =
        finiteDimensionalExponential
          (LieModule.toEnd ℂ StandardSl3.Algebra V X.toSpecialLinear)) :
    SU3ExponentiallyIntegratedStandardLieModel rho where
  finiteDimensional := inferInstance
  lieRingModule := inferInstance
  lieModule := inferInstance
  parameter := CompactRealForm (Fin 3)
  generation :=
    SpecialUnitaryGeneration.compactExponentialGeneration (N := 3)
  toComplexLie := CompactRealForm.toSpecialLinear
  action_generator := hAction

namespace SU2DifferentiatedExponentialAction

/-- Upgrade the representation-dependent `SU(2)` certificate using the
Lean-checked compact exponential generation theorem. -/
def toGeneratedModelOfCompactGeneration
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    {rho : Representation ℂ SU2 V}
    (D : SU2DifferentiatedExponentialAction rho) :
    SU2GeneratedExponentialStandardLieModel rho := by
  letI : FiniteDimensional ℂ V := D.finiteDimensional
  letI : LieRingModule StandardSl2.Algebra V := D.lieRingModule
  letI : LieModule ℂ StandardSl2.Algebra V := D.lieModule
  exact su2GeneratedModelOfCompactGeneration rho D.action_exp

end SU2DifferentiatedExponentialAction

namespace SU3DifferentiatedExponentialAction

/-- Upgrade the representation-dependent `SU(3)` certificate using the
Lean-checked compact exponential generation theorem. -/
def toExponentialModelOfCompactGeneration
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    {rho : Representation ℂ SU3 V}
    (D : SU3DifferentiatedExponentialAction rho) :
    SU3ExponentiallyIntegratedStandardLieModel rho := by
  letI : FiniteDimensional ℂ V := D.finiteDimensional
  letI : LieRingModule StandardSl3.Algebra V := D.lieRingModule
  letI : LieModule ℂ StandardSl3.Algebra V := D.lieModule
  exact su3ModelOfCompactGeneration rho D.action_exp

end SU3DifferentiatedExponentialAction

end

end SpecialUnitaryLieAlgebra
end GUT
