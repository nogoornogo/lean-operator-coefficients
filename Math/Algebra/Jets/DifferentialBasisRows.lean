import Math.Algebra.Jets.TwoSidedDifferentialNormalForm
import Mathlib.LinearAlgebra.Basis.Defs

/-! Full nonlinear equation and divergence rows on a basis. Both equation
multipliers and every derivative word are retained, at every order. -/
namespace Math.DifferentialBasisRows
set_option autoImplicit false
noncomputable section
variable {A I ι κ : Type*} [Ring A] [Algebra ℂ A]
  (D : I → A →ₗ[ℂ] A) (b : Module.Basis ι ℂ A) (seed : κ → A)

abbrev Row (I ι κ : Type*) := (ι × ι × κ × List I) ⊕ (I × ι)

def relation : Row I ι κ → A
  | .inl (i,j,k,w) => b i * VariationalIBP.word D w (seed k) * b j
  | .inr (i,j) => D i (b j)

def span : Submodule ℂ A := Submodule.span ℂ (Set.range (relation D b seed))

theorem equation_mem (i j : ι) (k : κ) (w : List I) :
    b i * VariationalIBP.word D w (seed k) * b j ∈ span D b seed :=
  Submodule.subset_span ⟨.inl (i,j,k,w),rfl⟩

theorem derivative_mem (i : I) (j : ι) : D i (b j) ∈ span D b seed :=
  Submodule.subset_span ⟨.inr (i,j),rfl⟩

theorem normal_mem (a c : A) (k : κ) (w : List I) :
    a * VariationalIBP.word D w (seed k) * c ∈ span D b seed := by
  have ha : a ∈ Submodule.span ℂ (Set.range b) := by rw [b.span_eq]; trivial
  have hc : c ∈ Submodule.span ℂ (Set.range b) := by rw [b.span_eq]; trivial
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨i,rfl⟩ := ha
    induction hc using Submodule.span_induction with
    | mem c hc => obtain ⟨j,rfl⟩ := hc; exact equation_mem D b seed i j k w
    | zero => simp
    | add c d hc hd ihc ihd =>
      simpa only [mul_add] using (span D b seed).add_mem ihc ihd
    | smul z c hc ih =>
      simpa only [mul_smul_comm] using (span D b seed).smul_mem z ih
  | zero => simp
  | add a d ha hd iha ihd =>
    simpa only [add_mul] using (span D b seed).add_mem iha ihd
  | smul z a ha ih =>
    simpa only [smul_mul_assoc] using (span D b seed).smul_mem z ih

theorem derivative_all_mem (i : I) (a : A) : D i a ∈ span D b seed := by
  have ha : a ∈ Submodule.span ℂ (Set.range b) := by rw [b.span_eq]; trivial
  induction ha using Submodule.span_induction with
  | mem a ha => obtain ⟨j,rfl⟩ := ha; exact derivative_mem D b seed i j
  | zero => simpa only [map_zero] using (span D b seed).zero_mem
  | add a c ha hc iha ihc => simpa only [map_add] using (span D b seed).add_mem iha ihc
  | smul z a ha ih => simpa only [map_smul] using (span D b seed).smul_mem z ih

theorem span_eq (leibniz : ∀ i p q, D i (p*q) = D i p*q + p*D i q) :
    span D b seed = TwoSidedDifferential.combined D (Set.range seed) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro p ⟨r,rfl⟩
    cases r with
    | inl r =>
      obtain ⟨i,j,k,w⟩ := r
      exact Submodule.mem_sup_left (TwoSidedDifferential.normal_mem D _ _ _ _ _ ⟨k,rfl⟩)
    | inr r =>
      obtain ⟨i,j⟩ := r
      exact Submodule.mem_sup_right ⟨Finsupp.single i (b j), VariationalIBP.divergence_single D _ _⟩
  · apply sup_le
    · rw [TwoSidedDifferential.relations_eq_span_normal D _ leibniz]
      apply Submodule.span_le.mpr
      rintro p ⟨a,c,r,w,⟨k,rfl⟩,rfl⟩
      exact normal_mem D b seed a c k w
    · rintro p ⟨c,rfl⟩
      induction c using Finsupp.induction_linear with
      | zero => simp
      | add c d hc hd => simpa only [map_add] using (span D b seed).add_mem hc hd
      | single i a =>
        simpa only [VariationalIBP.divergence_single] using derivative_all_mem D b seed i a

end
end Math.DifferentialBasisRows
