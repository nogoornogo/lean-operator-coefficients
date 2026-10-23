import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Complex.Basic

/-! Spectral basis for a symmetric conjugate-linear map, using real spectral theory. -/
namespace Math.AntilinearSpectral
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open Module
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

def realMap (T : E → E) (ha : ∀ x y, T (x + y) = T x + T y)
    (hs : ∀ (z : ℂ) x, T (z • x) = conj z • T x) : E →ₗ[ℝ] E where
  toFun := T
  map_add' := ha
  map_smul' r x := by
    simpa using hs (r : ℂ) x

theorem exists_unit_eigenvector [Nontrivial E] (T : E → E)
    (ha : ∀ x y, T (x + y) = T x + T y)
    (hs : ∀ (z : ℂ) x, T (z • x) = conj z • T x)
    (hh : ∀ x y, inner ℂ (T x) y = inner ℂ (T y) x) :
    ∃ (v : E) (r : ℝ), ‖v‖ = 1 ∧ T v = (r : ℂ) • v := by
  let := InnerProductSpace.complexToReal (G := E)
  let : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
  have hR : (realMap T ha hs).IsSymmetric := by
    intro x y
    change (inner ℂ (T x) y).re = (inner ℂ x (T y)).re
    rw [hh]
    exact (inner_re_symm (𝕜 := ℂ) x (T y)).symm
  obtain ⟨x, hx, hne⟩ := hR.hasEigenvalue_iSup_of_finiteDimensional.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hx
  let r : ℝ := ⨆ x : {x : E // x ≠ 0}, (inner ℝ (realMap T ha hs x) x) / ‖(x : E)‖ ^ 2
  refine ⟨(‖x‖⁻¹ : ℝ) • x, r, ?_, ?_⟩
  · simp [norm_smul, norm_ne_zero_iff.mpr hne]
  · change realMap T ha hs ((‖x‖⁻¹ : ℝ) • x) = (r : ℂ) • _
    rw [map_smul, hx]
    change (‖x‖⁻¹ : ℝ) • (r • x) = r • ((‖x‖⁻¹ : ℝ) • x)
    exact smul_comm _ _ _

theorem exists_basis (n : ℕ) (hn : finrank ℂ E = n) (T : E → E)
    (ha : ∀ x y, T (x + y) = T x + T y)
    (hs : ∀ (z : ℂ) x, T (z • x) = conj z • T x)
    (hh : ∀ x y, inner ℂ (T x) y = inner ℂ (T y) x) :
    ∃ (b : OrthonormalBasis (Fin n) ℂ E) (r : Fin n → ℝ),
      ∀ i, T (b i) = (r i : ℂ) • b i := by
  induction n generalizing E with
  | zero =>
    refine ⟨(stdOrthonormalBasis ℂ E).reindex (finCongr hn), fun _ => 0, ?_⟩
    intro i; exact Fin.elim0 i
  | succ n ih =>
    let : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
    obtain ⟨v, r, hv, hTv⟩ := exists_unit_eigenvector T ha hs hh
    have hv0 : v ≠ 0 := by intro h; simp [h] at hv
    let S : Submodule ℂ E := (ℂ ∙ v)ᗮ
    have hST : ∀ x : S, T x ∈ S := by
      intro x
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
      rw [hh, hTv, inner_smul_left]
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property]
      simp
    let TS : S → S := fun x => ⟨T x, hST x⟩
    have hdim : finrank ℂ S = n := by
      let : Fact (finrank ℂ E = n + 1) := ⟨hn⟩
      exact Submodule.finrank_orthogonal_span_singleton hv0
    obtain ⟨b, rb, hb⟩ := ih hdim TS
      (fun x y => Subtype.ext (ha x y))
      (fun z x => Subtype.ext (hs z x))
      (fun x y => hh x y)
    let w : Fin (n + 1) → E := Fin.cons v (fun i => (b i : E))
    have hw : Orthonormal ℂ w := by
      rw [orthonormal_iff_ite]
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simp [w, inner_self_eq_norm_sq_to_K, hv]
      · simpa [w, Fin.succ_ne_zero, Ne.symm (Fin.succ_ne_zero j)] using
          Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b j).property
      · simpa [w] using Submodule.mem_orthogonal_singleton_iff_inner_left.mp (b i).property
      · simpa [w] using orthonormal_iff_ite.mp b.orthonormal i j
    have hspan : ⊤ ≤ Submodule.span ℂ (Set.range w) := by
      rw [hw.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp [hn])]
    refine ⟨OrthonormalBasis.mk hw hspan, Fin.cons r rb, ?_⟩
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [w] using hTv
    · simpa [w, TS] using congrArg Subtype.val (hb i)

end
end Math.AntilinearSpectral
