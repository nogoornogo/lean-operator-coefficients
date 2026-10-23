import Math.RepresentationTheory.Lagrangian.AllOrderDerivativeCoordinates
import Math.Algebra.Jets.DifferentialBasisRows
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Derivative

/-! A closed all-degree interacting example. For the one-variable equation
lambda X^n = 0, all coefficient sequences are classified, including lambda=0. -/
namespace Math.PolynomialPotentialClassification
set_option autoImplicit false
noncomputable section
open Polynomial
abbrev A := Polynomial ℂ
def D : Empty → A →ₗ[ℂ] A := Empty.elim
def seed (coupling : ℂ) (n : ℕ) (_ : Unit) : A := coupling • (X^n)

def potential (coupling : ℂ) (n : ℕ) : A := (coupling/(n+1:ℂ)) • X^(n+1)

theorem potential_derivative (coupling : ℂ) (n : ℕ) :
    (potential coupling n).derivative = seed coupling n () := by
  have hn : (n+1:ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  rw [potential,Polynomial.derivative_smul,Polynomial.derivative_X_pow_succ,
    ← Polynomial.smul_eq_C_mul,smul_smul,div_mul_cancel₀ _ hn]
  rfl

def input (coupling : ℂ) (n : ℕ) : DerivativeInterface.Input Unit A where
  action := Representation.trivial ℂ Unit A
  relations := TwoSidedDifferential.combined D (Set.range (seed coupling n))
  stable _ := le_refl _

def presentation (coupling : ℂ) (n : ℕ) :
    AllOrderDerivativeCoordinates.Presentation (ι := ℕ)
      (κ := DifferentialBasisRows.Row Empty ℕ Unit) (input coupling n) where
  basis := Polynomial.basisMonomials ℂ
  relation := DifferentialBasisRows.relation D (Polynomial.basisMonomials ℂ) (seed coupling n)
  relation_span := DifferentialBasisRows.span_eq D _ _ (fun i => i.elim)

abbrev Coordinates (coupling : ℂ) (n : ℕ) := (presentation coupling n).rows

theorem basis_value (k : ℕ) : Polynomial.basisMonomials ℂ k = (X^k : A) := by
  simp [Polynomial.coe_basisMonomials, Polynomial.monomial_one_right_eq_X_pow]

theorem evaluate_power (coupling : ℂ) (n : ℕ) (c : ℕ → ℂ) (k : ℕ) :
    (presentation coupling n).assemble c (X^k) = c k := by
  rw [← basis_value]
  exact (presentation coupling n).assemble_basis c k

theorem equation_evaluation (coupling : ℂ) (n : ℕ) (c : ℕ → ℂ) (i j : ℕ) :
    (presentation coupling n).assemble c
      (Polynomial.basisMonomials ℂ i * seed coupling n () * Polynomial.basisMonomials ℂ j) =
    coupling*c (n+(i+j)) := by
  have he : Polynomial.basisMonomials ℂ i * seed coupling n () * Polynomial.basisMonomials ℂ j =
      coupling • (X^(n+(i+j)) : A) := by
    rw [basis_value,basis_value]
    simp only [seed, mul_smul_comm, smul_mul_assoc, ← pow_add]
    congr 2
    omega
  rw [he,map_smul,evaluate_power]
  rfl

theorem coordinates_iff (coupling : ℂ) (n : ℕ) (c : ℕ → ℂ) :
    c ∈ Coordinates coupling n ↔ ∀ k, coupling*c (n+k) = 0 := by
  constructor
  · rintro ⟨hr,hg⟩ k
    have h := hr (.inl (0,k,(),[]))
    change (presentation coupling n).assemble c
      (Polynomial.basisMonomials ℂ 0 * seed coupling n () * Polynomial.basisMonomials ℂ k) = 0 at h
    simpa only [equation_evaluation,zero_add] using h
  · intro h
    constructor
    · intro r
      cases r with
      | inl r =>
        obtain ⟨i,j,k,w⟩ := r
        cases w with
        | nil => exact (equation_evaluation coupling n c i j).trans (h (i+j))
        | cons e w => exact e.elim
      | inr r => exact r.1.elim
    · intro g i
      change (presentation coupling n).assemble c (Polynomial.basisMonomials ℂ i) = c i
      exact (presentation coupling n).assemble_basis c i

theorem all_degree_prescribed_iff (coupling : ℂ) (n : ℕ) (c : ℕ → ℂ) :
    (∃ f : (input coupling n).Coefficient, ∀ k, f.val (X^k) = c k) ↔
      ∀ k, coupling*c (n+k) = 0 := by
  have h := (presentation coupling n).prescribed_iff c
  simp only [show (presentation coupling n).basis = Polynomial.basisMonomials ℂ from rfl,
    basis_value] at h
  exact h.trans (coordinates_iff coupling n c)

theorem zero_coupling (n : ℕ) (c : ℕ → ℂ) : c ∈ Coordinates 0 n :=
  (coordinates_iff 0 n c).mpr (fun _ => zero_mul _)

theorem nonzero_coupling (coupling : ℂ) (n : ℕ) (hc : coupling ≠ 0) (c : ℕ → ℂ) :
    c ∈ Coordinates coupling n ↔ ∀ k, c (n+k) = 0 := by
  rw [coordinates_iff]
  simp only [mul_eq_zero, hc, false_or]

theorem target_value_iff (coupling : ℂ) (n m : ℕ) (c : ℂ) :
    (∃ f : (input coupling n).Coefficient, f.val (X^m) = c) ↔
      coupling = 0 ∨ m < n ∨ c = 0 := by
  constructor
  · rintro ⟨f,hf⟩
    by_cases hc : coupling = 0
    · exact Or.inl hc
    by_cases hm : m < n
    · exact Or.inr (Or.inl hm)
    have h := (all_degree_prescribed_iff coupling n (fun k => f.val (X^k))).mp ⟨f,fun _ => rfl⟩ (m-n)
    have he : n+(m-n) = m := by omega
    rw [he,hf] at h
    exact Or.inr (Or.inr ((mul_eq_zero.mp h).resolve_left hc))
  · intro h
    let q : ℕ → ℂ := fun k => if k=m then c else 0
    have hq : ∀ k, coupling*q (n+k) = 0 := by
      intro k
      rcases h with hc | hm | hc
      · simp [hc]
      · have he : n+k ≠ m := by omega
        simp [q,he]
      · simp [q,hc]
    obtain ⟨f,hf⟩ := (all_degree_prescribed_iff coupling n q).mpr hq
    exact ⟨f,by simpa [q] using hf m⟩

def lowEquivalence (coupling : ℂ) (n : ℕ) (hc : coupling ≠ 0) :
    Coordinates coupling n ≃ₗ[ℂ] (Fin n → ℂ) where
  toFun c i := c.val i.val
  invFun c := ⟨fun k => if h : k < n then c ⟨k,h⟩ else 0, by
    apply (nonzero_coupling coupling n hc _).mpr
    intro k
    simp only [show ¬n+k<n by omega, dite_false]⟩
  left_inv c := by
    apply Subtype.ext
    funext k
    by_cases hk : k < n
    · simp only [hk,dite_true]
    · simp only [hk,dite_false]
      have he : n+(k-n)=k := by omega
      simpa only [he] using ((nonzero_coupling coupling n hc c.val).mp c.property (k-n)).symm
  right_inv c := by funext i; simp only [i.isLt,dite_true]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def freeEquivalence (n : ℕ) : Coordinates 0 n ≃ₗ[ℂ] (ℕ → ℂ) where
  toFun := Subtype.val
  invFun c := ⟨c,zero_coupling n c⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- An input-independent cutoff cannot capture every polynomial interaction. -/
theorem no_uniform_degree_cutoff (bound : ℕ) :
    ∃ n, ∃ f : (input 1 n).Coefficient, f.val (X^(bound+1)) = 1 := by
  refine ⟨bound+2,?_⟩
  exact (target_value_iff 1 (bound+2) (bound+1) 1).mpr (Or.inr (Or.inl (by omega)))

/-- Even one fixed zero-interaction input has coefficients invisible at any
given finite order, so an infinite presentation is not a finite table. -/
theorem free_input_no_cutoff (bound : ℕ) :
    ∃ f : (input 0 1).Coefficient,
      f.val (X^(bound+1)) = 1 ∧ ∀ k ≤ bound, f.val (X^k) = 0 := by
  let q : ℕ → ℂ := fun k => if k=bound+1 then 1 else 0
  obtain ⟨f,hf⟩ := (all_degree_prescribed_iff 0 1 q).mpr (fun _ => zero_mul _)
  refine ⟨f,?_,?_⟩
  · simpa [q] using hf (bound+1)
  · intro k hk
    have he : k ≠ bound+1 := by omega
    simpa [q,he] using hf k

end
end Math.PolynomialPotentialClassification
