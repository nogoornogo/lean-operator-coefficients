import Math.LieAlgebras.SparseMatrixCertificate
import Math.LieAlgebras.GeneratedLieSpan
import Mathlib.Algebra.Lie.OfAssociative

/-!
# From checked sparse witnesses to an actual generated matrix Lie algebra

Only Boolean equalities discharged by Lean are accepted. Arbitrary generator
programs may propose the data, but cannot supply the soundness theorem.
-/

set_option autoImplicit false

namespace Math.MatrixLieCertificate

open SparseMatrixCertificate

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [DecidableEq n] [Fintype n] {m r : ℕ}

def checkOrigin (v : Fin m → Code n) (g : Fin r → Code n)
    (origin : Fin m → Fin r ⊕ (Fin r × Fin m)) (i : Fin m) : Bool :=
  match origin i with
  | .inl j => checkEq (v i) (g j)
  | .inr p => decide (p.2.val < i.val) && checkEq (v i) (bracket (g p.1) (v p.2))

variable (K : Type*) [Field K]

omit [Fintype n] in
theorem realize_eq_of_check (a b : Code n) (h : checkEq a b = true) :
    realize K a = realize K b :=
  congrArg (fun M : Matrix n n ℤ => M.map (Int.castRingHom K)) (checkEq_sound a b h)

theorem generated_mem (v : Fin m → Code n) (g : Fin r → Code n)
    (origin : Fin m → Fin r ⊕ (Fin r × Fin m))
    (h : ∀ i, checkOrigin v g origin i = true) :
    ∀ i, realize K (v i) ∈ LieSubalgebra.lieSpan K (Matrix n n K)
      (Set.range fun j => realize K (g j)) := by
  apply GeneratedLieSpan.mem_of_provenance _ _ origin
  intro i
  have hc := h i
  cases ho : origin i with
  | inl j =>
    exact realize_eq_of_check K (v i) (g j)
      (by simpa [checkOrigin, ho] using hc)
  | inr p =>
    have hc' : p.2.val < i.val ∧ checkEq (v i) (bracket (g p.1) (v p.2)) = true := by
      simpa [checkOrigin, ho] using hc
    refine ⟨hc'.1, ?_⟩
    change realize K (v i) = realize K (g p.1) * realize K (v p.2) -
      realize K (v p.2) * realize K (g p.1)
    exact (realize_eq_of_check K _ _ hc'.2).trans (realize_bracket K _ _)

theorem span_eq_generated (v : Fin m → Code n) (g : Fin r → Code n)
    (origin : Fin m → Fin r ⊕ (Fin r × Fin m))
    (generatorIndex : Fin r → Fin m) (coeff : Fin r → Fin m → List (Fin m × ℤ))
    (horigin : ∀ i, checkOrigin v g origin i = true)
    (hgen : ∀ i, checkEq (g i) (v (generatorIndex i)) = true)
    (hclose : ∀ i j, checkEq (bracket (g i) (v j)) (combination v (coeff i j)) = true) :
    Submodule.span K (Set.range fun i => realize K (v i)) =
      (LieSubalgebra.lieSpan K (Matrix n n K) (Set.range fun i => realize K (g i)) :
        Submodule K (Matrix n n K)) := by
  apply GeneratedLieSpan.span_eq_lieSpan
  · intro i
    rw [realize_eq_of_check K _ _ (hgen i)]
    exact Submodule.subset_span (Set.mem_range_self (generatorIndex i))
  · exact generated_mem K v g origin horigin
  · intro i j
    change realize K (g i) * realize K (v j) - realize K (v j) * realize K (g i) ∈ _
    rw [← realize_bracket, realize_eq_of_check K _ _ (hclose i j)]
    exact realize_combination_mem K v _ _ fun k =>
      Submodule.subset_span (Set.mem_range_self k)

variable [CharZero K]

theorem finrank_generated (v d : Fin m → Code n) (scale : Fin m → ℤ)
    (g : Fin r → Code n) (origin : Fin m → Fin r ⊕ (Fin r × Fin m))
    (generatorIndex : Fin r → Fin m) (coeff : Fin r → Fin m → List (Fin m × ℤ))
    (horigin : ∀ i, checkOrigin v g origin i = true)
    (hgen : ∀ i, checkEq (g i) (v (generatorIndex i)) = true)
    (hclose : ∀ i j, checkEq (bracket (g i) (v j)) (combination v (coeff i j)) = true)
    (hnz : ∀ i, scale i ≠ 0)
    (hpair : ∀ i j, pairing (d i) (v j) = if i = j then scale i else 0) :
    Module.finrank K
      (LieSubalgebra.lieSpan K (Matrix n n K) (Set.range fun i => realize K (g i))).toSubmodule = m := by
  have hs := span_eq_generated K v g origin generatorIndex coeff horigin hgen hclose
  have hd := finrank_span_eq_card (linearIndependent_of_pairing (K := K) v d scale hnz hpair)
  rw [hs] at hd
  simpa using hd

end Math.MatrixLieCertificate
