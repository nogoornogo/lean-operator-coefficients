import Math.RepresentationTheory.Content.PatternScalarWeights
import Math.RepresentationTheory.Exterior.BinaryPatternExterior

/-! Actual weight slices of an exterior power of two opposite scalar
species. Fixed total occupation and circle weight determine both counts;
the slice is the tensor of their exterior powers. -/
namespace Math.BinaryScalarExteriorSlice
set_option autoImplicit false
noncomputable section
open Representation FiniteExteriorExhaustion PatternScalarWeights
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
variable {G K : Type*} [Group G] [Group K]
  {V : Fin 2 → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  (r : ∀ s, Representation ℂ (G × K) (V s)) (t : Circle →* G)

def weights (s : Fin 2) : ℤ := if s=0 then 1 else -1

theorem weight_formula (n : ℕ) (c : Occupation (S := Fin 2) n) :
    occupationWeight weights n c=(c.val 0).val-(c.val 1).val := by
  simp [occupationWeight, weights, Fin.sum_univ_two, sub_eq_add_neg]

theorem weight_injective (n : ℕ) : Function.Injective (occupationWeight weights n) := by
  intro c d he
  have hc := occupation_sum n c
  have hd := occupation_sum n d
  simp only [Fin.sum_univ_two] at hc hd
  rw [weight_formula, weight_formula] at he
  have h0 : (c.val 0).val=(d.val 0).val := by omega
  have h1 : (c.val 1).val=(d.val 1).val := by omega
  apply Subtype.ext
  funext s
  apply Fin.ext
  fin_cases s
  · exact h0
  · exact h1

abbrev pattern (p q : ℕ) := BinaryPatternExterior.pattern (0 : Fin 2) 1 p q
abbrev occupation (p q : ℕ) := FiniteExteriorExhaustion.occupation (p+q) (pattern p q)

theorem count_zero (p q : ℕ) : ((occupation p q).val 0).val = p := by
  change (Finset.univ.filter (fun i => pattern p q i=0)).card=p
  rw [Finset.card_filter, Fin.sum_univ_add]
  simp [pattern, BinaryPatternExterior.pattern]

theorem count_one (p q : ℕ) : ((occupation p q).val 1).val = q := by
  change (Finset.univ.filter (fun i => pattern p q i=1)).card=q
  rw [Finset.card_filter, Fin.sum_univ_add]
  simp [pattern, BinaryPatternExterior.pattern]

theorem selected_weight (p q : ℕ) :
    occupationWeight weights (p+q) (occupation p q)=(p : ℤ)-q := by
  rw [weight_formula, count_zero, count_one]

def representativeEquiv (p q : ℕ) : Representation.Equiv
    (OccupationExteriorDecomposition.block r (p+q) (occupation p q))
    (PatternExteriorSource.representation r (pattern p q)) :=
  PatternMultiplicityEquiv.equiv r _ _ (fun s =>
    congrArg Fin.val (congrFun (representative_counts (p+q) (occupation p q)) s))

variable (hr : ∀ s z x, r s (t z,1) x=(z : ℂ)^(weights s) • x)

/-- Full retained-action equivalence. No basis, exterior dimension,
character coefficient or numerical multiplicity is evaluated. -/
@[reducible] local instance (p q : ℕ) : AddCommGroup
    ((⋀[ℂ]^p (V 0)) ⊗[ℂ] (⋀[ℂ]^q (V 1))) := Module.addCommMonoidToAddCommGroup ℂ

def equivalence (p q : ℕ) : Representation.Equiv
    (TorusWeightSlice.action (PatternExteriorSource.Full r (n := p+q)) t ((p : ℤ)-q))
    (TorusWeightSlice.residual (((r 0).exteriorPower p).tprod ((r 1).exteriorPower q))) :=
  (TorusWeightSlice.castWeight (PatternExteriorSource.Full r (n := p+q)) t
    (selected_weight p q).symm).trans
  ((PatternScalarWeights.equivalence r t weights hr (p+q) (occupation p q)
    (fun d hd => weight_injective (p+q) hd)).trans
  ((SplitRepresentationProjection.restrictEquiv (representativeEquiv r p q)
    (MonoidHom.inr G K)).trans
    (SplitRepresentationProjection.restrictEquiv
      (BinaryPatternExterior.equiv r 0 1 p q (by decide)).symm (MonoidHom.inr G K))))

include hr in
theorem absent_zero (n : ℕ) (k : ℤ)
    (hk : ¬∃ p q : ℕ, p+q=n ∧ (p : ℤ)-q=k)
    (x : TorusWeightSlice.Space (PatternExteriorSource.Full r (n := n)) t k) : x=0 := by
  apply PatternScalarWeights.absent_zero r t weights hr n k _ x
  intro c he
  apply hk
  refine ⟨(c.val 0).val,(c.val 1).val, ?_, ?_⟩
  · simpa only [Fin.sum_univ_two] using occupation_sum n c
  · exact (weight_formula n c).symm.trans he

end
end Math.BinaryScalarExteriorSlice
