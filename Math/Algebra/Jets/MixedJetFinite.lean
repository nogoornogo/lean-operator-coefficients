import Math.Algebra.Jets.MixedJetGrading
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Fixed mixed jet grades are finite for finite component/direction sets.
The ambient jet algebra itself remains unbounded. -/
namespace Math.MixedJetAlgebra
set_option autoImplicit false
noncomputable section
open ScalarJetAlgebra

variable {F B I : Type*} {n m : ℕ}

theorem odd_order_le (f : Fin n → Index F I) (b : Fin m → Index B I) (k : Fin n) :
    order (f k).2 ≤ wordOrder f b := by
  exact (Finset.single_le_sum (fun i _ => Nat.zero_le (order (f i).2)) (Finset.mem_univ k)).trans
    (Nat.le_add_right _ _)

theorem even_order_le (f : Fin n → Index F I) (b : Fin m → Index B I) (k : Fin m) :
    order (b k).2 ≤ wordOrder f b := by
  exact (Finset.single_le_sum (fun i _ => Nat.zero_le (order (b i).2)) (Finset.mem_univ k)).trans
    (Nat.le_add_left _ _)

theorem finite_indices_le (S I : Type*) [Finite S] [Finite I] (d : ℕ) :
    Finite {j : Index S I // order j.2 ≤ d} := by
  let A := {α : I →₀ ℕ // order α ≤ d}
  have : Finite A := (Finsupp.finite_of_nat_weight_le (fun _ : I => 1)
    (fun _ => by decide) d).to_subtype
  exact Finite.of_injective (fun j : {j : Index S I // order j.2 ≤ d} =>
    (j.val.1, (⟨j.val.2, j.property⟩ : A))) (by
      intro a b h
      apply Subtype.ext
      exact Prod.ext (congrArg (fun x : S × A => x.1) h)
        (congrArg (fun x : S × A => x.2.val) h))

theorem finite_generators [Finite F] [Finite B] [Finite I] (n m d : ℕ) :
    (generators F B I n m d).Finite := by
  classical
  let T := {x : (Fin n → Index F I) × (Fin m → Index B I) // wordOrder x.1 x.2 = d}
  have : Finite {j : Index F I // order j.2 ≤ d} := finite_indices_le F I d
  have : Finite {j : Index B I // order j.2 ≤ d} := finite_indices_le B I d
  let encode (x : T) :
      (Fin n → {j : Index F I // order j.2 ≤ d}) × (Fin m → {j : Index B I // order j.2 ≤ d}) :=
    (fun k => ⟨x.val.1 k, (odd_order_le x.val.1 x.val.2 k).trans_eq x.property⟩,
     fun k => ⟨x.val.2 k, (even_order_le x.val.1 x.val.2 k).trans_eq x.property⟩)
  have hi : Function.Injective encode := by
    intro x y h
    apply Subtype.ext
    apply Prod.ext
    · funext k
      exact congrArg Subtype.val (congrFun (congrArg Prod.fst h) k)
    · funext k
      exact congrArg Subtype.val (congrFun (congrArg Prod.snd h) k)
  have : Finite T := Finite.of_injective encode hi
  have he : generators F B I n m d = Set.range (fun x : T => word x.val.1 x.val.2) := by
    ext p
    constructor
    · rintro ⟨f, b, hf, rfl⟩
      exact ⟨⟨(f, b), hf⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x.val.1, x.val.2, x.property, rfl⟩
  rw [he]
  exact Set.finite_range _

instance grade_finiteDimensional [Finite F] [Finite B] [Finite I] (n m d : ℕ) :
    FiniteDimensional ℂ (grade F B I n m d) := by
  exact FiniteDimensional.span_of_finite ℂ (finite_generators n m d)

end
end Math.MixedJetAlgebra
