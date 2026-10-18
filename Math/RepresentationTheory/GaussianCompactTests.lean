import Math.RepresentationTheory.RationalCompactTests
import Math.LinearAlgebra.GaussianRational

/-! Explicit Gaussian-rational matrices for the exhaustive compact tests. -/
namespace Math.GaussianCompactTests
set_option autoImplicit false
open GaussianRational Matrix

abbrev K := Scalar

def sample : K := ⟨3/5,4/5⟩

@[simp] theorem sample_embed : embed sample = (RationalCircleTests.sample : ℂ) := by
  simp [sample, RationalCircleTests.sample]
  ring

def torus : Matrix (Fin 2) (Fin 2) K := !![sample,0;0,sample⁻¹]
def mix : Matrix (Fin 2) (Fin 2) K :=
  !![⟨1/2,1/2⟩,⟨1/2,1/2⟩;⟨-1/2,1/2⟩,⟨1/2,-1/2⟩]
def weak (b : Bool) : Matrix (Fin 2) (Fin 2) K := if b then mix * torus * mixᴴ else torus

theorem torus_embed : torus.map embed = (TauCeti.SU2.torusHom RationalCircleTests.sample).val := by
  change torus.map embed = TauCeti.SU2.torusMatrix RationalCircleTests.sample
  have hi : embed sample⁻¹ = ((RationalCircleTests.sample : ℂ))⁻¹ :=
    (map_inv₀ embed.toRingHom sample).trans (congrArg (fun z : ℂ => z⁻¹) sample_embed)
  ext i j
  fin_cases i <;> fin_cases j <;>
    first | exact sample_embed | exact map_zero embed | exact hi

theorem mix_embed : mix.map embed = TwoCircleGeneration.mix.val := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mix, TwoCircleGeneration.mix]
  all_goals ring

theorem weak_embed (b : Bool) : (weak b).map embed = (RationalCompactTests.weak b).val := by
  cases b
  · exact torus_embed
  · change (mix * torus * mixᴴ).map embed =
      TwoCircleGeneration.mix.val * (TauCeti.SU2.torusHom RationalCircleTests.sample).val *
        star TwoCircleGeneration.mix.val
    rw [Matrix.map_mul, Matrix.map_mul, mix_embed, torus_embed]
    congr 1
    ext i j
    exact (embed_star (mix j i)).trans (congrArg star (congrFun (congrFun mix_embed j) i))

def plane (i : Fin 3) (u : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K := match i with
  | 0 => !![u 0 0,u 0 1,0;u 1 0,u 1 1,0;0,0,1]
  | 1 => !![u 0 0,0,u 0 1;0,1,0;u 1 0,0,u 1 1]
  | 2 => !![1,0,0;0,u 0 0,u 0 1;0,u 1 0,u 1 1]

def color (i : Fin 3 × Bool) := plane i.1 (weak i.2)

theorem plane_embed (i : Fin 3) (u : Matrix (Fin 2) (Fin 2) K)
    (v : TauCeti.SU2) (h : u.map embed = v.val) :
    (plane i u).map embed = ColorPlaneCircles.planeMatrix i v := by
  fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;>
    simp [-embed_apply, plane, ColorPlaneCircles.planeMatrix] <;>
    exact congrFun (congrFun h _) _

theorem color_embed (i : Fin 3 × Bool) : (color i).map embed = (RationalCompactTests.color i).val := by
  exact (plane_embed i.1 (weak i.2) (RationalCompactTests.weak i.2) (weak_embed i.2)).trans
    (ColorPlaneCircles.embedding_matrix i.1 _).symm

end Math.GaussianCompactTests
