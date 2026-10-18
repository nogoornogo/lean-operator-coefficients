import Physics.StandardModel.Operators.DuueResidualCompleteness

open Math

/-! Normalized local interpretation of Li D.6 and its conjugate: D,E,U,U.
The two brackets are interpreted in supplied normalized spinor coordinates.
No amplitude or physical conjugation identification is inferred. -/
namespace GUT.LiDuueConvention
set_option autoImplicit false
noncomputable section
open Representation SMEpsilonTensor FourDoubletInvariant
open scoped TensorProduct

def paperSymmetric (d u v : Color) (s t x y : Space) : ℂ :=
  eps3 d u v * eps s x * eps t y
def paperAlternating (d u v : Color) (s t x y : Space) : ℂ :=
  eps3 d u v * eps s t * eps x y

/-- Conjugation of the normalized local coordinates, not a model-specific
identification of antiparticle flavor spaces. -/
theorem conjugate_symmetric (d u v : Color) (s t x y : Space) :
    star (paperSymmetric d u v s t x y) =
      paperSymmetric (star d) (star u) (star v) (star s) (star t) (star x) (star y) := by
  simp [paperSymmetric, eps3, eps]
theorem conjugate_alternating (d u v : Color) (s t x y : Space) :
    star (paperAlternating d u v s t x y) =
      paperAlternating (star d) (star u) (star v) (star s) (star t) (star x) (star y) := by
  simp [paperAlternating, eps3, eps]

theorem reorder_symmetric (d u v : Color) (s t x y : Space) :
    paperSymmetric d u v s t x y = eps3 u v d * eps x s * eps y t := by
  simp [paperSymmetric, eps3, eps]; ring
theorem reorder_alternating (d u v : Color) (s t x y : Space) :
    paperAlternating d u v s t x y = eps3 u v d * eps x y * eps s t := by
  simp [paperAlternating, eps3]; ring

variable {H U D E : Type*} [Group H] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup D] [Module ℂ D] [AddCommGroup E] [Module ℂ E]
  (u : Representation ℂ H U) (d : Representation ℂ H D) (e : Representation ℂ H E)

def symmetricSource (k : DuueOrderedCompleteness.Residual u d e) :=
  (- (1/2 : ℂ)) • (k + DuueResidualCompleteness.swap u d e k)
def alternatingSource (k : DuueOrderedCompleteness.Residual u d e) :=
  (1/4 : ℂ) • (k - DuueResidualCompleteness.swap u d e k)

theorem source_symmetries (k : DuueOrderedCompleteness.Residual u d e)
    (x y : U) (h : D) (j : E) :
    symmetricSource u d e k ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) =
      symmetricSource u d e k ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) ∧
    alternatingSource u d e k ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) =
      -alternatingSource u d e k ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) := by
  constructor <;> simp [symmetricSource, alternatingSource,
    DuueResidualCompleteness.swap_apply, smul_eq_mul] <;> ring

/-- Actual two-term alternation of the two printed seeds, after the even
D,E,U,U to U,U,D,E permutation; color and Fermi signs cancel. -/
theorem local_reconstruction (k : DuueOrderedCompleteness.Residual u d e)
    (x y : U) (h : D) (j : E) (s t v w : Space) :
    let p := ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j))
    let p' := ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j))
    eps s v * eps t w * symmetricSource u d e k p +
      eps t v * eps s w * symmetricSource u d e k p' +
      eps s t * eps v w * alternatingSource u d e k p +
      eps t s * eps v w * alternatingSource u d e k p' =
    eps s t * eps v w * k p + eps s v * eps t w *
      (-k p - DuueResidualCompleteness.swap u d e k p) := by
  simp [symmetricSource, alternatingSource, DuueResidualCompleteness.swap_apply,
    smul_eq_mul, eps]
  ring
end
end GUT.LiDuueConvention
