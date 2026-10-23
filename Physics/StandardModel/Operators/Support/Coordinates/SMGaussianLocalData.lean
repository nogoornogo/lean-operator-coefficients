import Physics.StandardModel.Operators.Support.Coordinates.SMRationalLocalKernel
import Math.RepresentationTheory.Weights.GaussianCompactTests

/-! The exhaustive local samples have explicit Gaussian rational coordinates. -/
namespace Physics.SMGaussianLocalData
set_option autoImplicit false
open Math GaussianRational Matrix
abbrev K := Scalar

structure Data where
  color : Matrix (Fin 3) (Fin 3) K
  weak : Matrix (Fin 2) (Fin 2) K
  phase : K
  spin : Matrix (Fin 2) (Fin 2) K

def spinSample (n : ℕ) (a : WeylRealTransvections.Index × Fin (n+1)) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.transvection a.1.1.val.1 a.1.1.val.2
    ((if a.1.2 then QuadraticAlgebra.omega else 1) * (a.2.val : K))

def data (n : ℕ) : SMRationalLocalKernel.Index n → Data
  | .inl i => ⟨GaussianCompactTests.color i,1,1,1⟩
  | .inr (.inl b) => ⟨1,GaussianCompactTests.weak b,1,1⟩
  | .inr (.inr (.inl _)) => ⟨1,1,GaussianCompactTests.sample,1⟩
  | .inr (.inr (.inr a)) => ⟨1,1,1,spinSample n a⟩

theorem spin_embed (n : ℕ) (a : WeylRealTransvections.Index × Fin (n+1)) :
    (spinSample n a).map embed = (WeylRealTransvections.tests n a).val := by
  change (Matrix.transvection a.1.1.val.1 a.1.1.val.2
    ((if a.1.2 then QuadraticAlgebra.omega else 1) * (a.2.val : K))).map embed =
    Matrix.transvection a.1.1.val.1 a.1.1.val.2
      (WeylRealTransvections.phase a.1.2 * (a.2.val : ℂ))
  have ho : embed (QuadraticAlgebra.omega : K) = Complex.I := by simp [QuadraticAlgebra.omega]
  rcases a with ⟨⟨pair,b⟩,k⟩
  cases b <;> ext i j <;>
    simp [-embed_apply, WeylRealTransvections.phase, Matrix.transvection,
      Matrix.single_apply, Matrix.one_apply]
  all_goals split_ifs <;> simp only [map_mul, map_natCast, map_zero, ho]

variable (n : ℕ) (i : SMRationalLocalKernel.Index n)

theorem color_embed : (data n i).color.map embed =
    ((SMRationalLocalKernel.tests n i).1.1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  rcases i with i | (b | (u | a))
  · exact GaussianCompactTests.color_embed i
  all_goals ext j k; simp [-embed_apply, data, SMRationalLocalKernel.tests,
    SMIntegralLocalWeights.weak, SMIntegralLocalWeights.hyper,
    SMIntegralLocalWeights.spin, Matrix.one_apply]

theorem weak_embed : (data n i).weak.map embed =
    ((SMRationalLocalKernel.tests n i).1.2.1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rcases i with c | (b | (u | a))
  · ext j k; simp [-embed_apply, data, SMRationalLocalKernel.tests, SMIntegralLocalWeights.color, Matrix.one_apply]
  · exact GaussianCompactTests.weak_embed b
  all_goals ext j k; simp [-embed_apply, data, SMRationalLocalKernel.tests,
    SMIntegralLocalWeights.hyper, SMIntegralLocalWeights.spin, Matrix.one_apply]

theorem phase_embed : embed (data n i).phase = ((SMRationalLocalKernel.tests n i).1.2.2 : ℂ) := by
  rcases i with c | (b | (u | a)) <;>
    simp [-embed_apply, data, SMRationalLocalKernel.tests, SMIntegralLocalWeights.color,
      SMIntegralLocalWeights.weak, SMIntegralLocalWeights.hyper, SMIntegralLocalWeights.spin,
      GaussianCompactTests.sample_embed]

theorem spin_data_embed : (data n i).spin.map embed =
    ((SMRationalLocalKernel.tests n i).2 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rcases i with c | (b | (u | a))
  all_goals first
    | exact spin_embed n a
    | (ext j k; simp [-embed_apply, data, SMRationalLocalKernel.tests, SMIntegralLocalWeights.color,
        SMIntegralLocalWeights.weak, SMIntegralLocalWeights.hyper, Matrix.one_apply])

end Physics.SMGaussianLocalData
