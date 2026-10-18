import Math.LieGroups.Torus.CircleHomLattice
import Mathlib.Tactic

/-!
# The character lattice of a finite compact torus

For a finite index type `d`, every continuous homomorphism
`(d -> Circle) -> Circle` is a unique Laurent monomial with integer exponent
vector `d -> Integer`.  The proof restricts to each coordinate circle, applies
`CircleHomLattice.existsUnique_eq_circlePowerHom`, and reconstructs every
torus point as the product of its coordinate inclusions.
-/

open scoped BigOperators

namespace Math
namespace CircleTorusCharacterLattice

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

abbrev Torus (d : Type*) := d -> Circle

/-- Include one coordinate circle in a finite product torus. -/
def coordinateHom (i : d) : Circle →ₜ* Torus d where
  toMonoidHom :=
    { toFun := fun z j => if j = i then z else 1
      map_one' := by
        funext j
        simp
      map_mul' := by
        intro z w
        funext j
        by_cases h : j = i <;> simp [h] }
  continuous_toFun := by
    apply continuous_pi
    intro j
    by_cases h : j = i
    · subst j
      simp only [ite_eq_left]
      fun_prop
    · simp only [ite_eq_right h]
      fun_prop

omit [Fintype d] in
@[simp]
theorem coordinateHom_apply (i : d) (z : Circle) (j : d) :
    coordinateHom i z j = if j = i then z else 1 := by
  rfl

/-- Every torus point is the product of its one-coordinate points. -/
theorem prod_coordinateHom (x : Torus d) :
    (∏ i, coordinateHom i (x i)) = x := by
  funext j
  rw [Fintype.prod_apply]
  simp

/-- The Laurent monomial associated to an integer exponent vector. -/
def torusCharacter (n : d -> ℤ) : Torus d →ₜ* Circle where
  toMonoidHom :=
    { toFun := fun x => ∏ i, x i ^ n i
      map_one' := by simp
      map_mul' := by
        intro x y
        simp_rw [Pi.mul_apply, mul_zpow]
        exact Finset.prod_mul_distrib }
  continuous_toFun := by
    fun_prop

omit [DecidableEq d] in
@[simp]
theorem torusCharacter_apply (n : d -> ℤ) (x : Torus d) :
    torusCharacter n x = ∏ i, x i ^ n i :=
  rfl

@[simp]
theorem torusCharacter_coordinateHom
    (n : d -> ℤ) (i : d) (z : Circle) :
    torusCharacter n (coordinateHom i z) = z ^ n i := by
  change (∏ j, (if j = i then z else 1) ^ n j) = z ^ n i
  simp

def coordinateRestriction
    (f : Torus d →ₜ* Circle) (i : d) : Circle →ₜ* Circle :=
  f.comp (coordinateHom i)

/-- Continuous characters of a finite compact torus are classified by a
unique integer exponent vector. -/
theorem existsUnique_eq_torusCharacter (f : Torus d →ₜ* Circle) :
    ∃! n : d -> ℤ, f = torusCharacter n := by
  have hcoord :
      ∀ i : d, ∃! n : ℤ,
        coordinateRestriction f i = CircleHomLattice.circlePowerHom n := by
    intro i
    exact CircleHomLattice.existsUnique_eq_circlePowerHom
      (coordinateRestriction f i)
  choose n hn hn_unique using hcoord
  refine ⟨n, ?_, ?_⟩
  · apply ContinuousMonoidHom.ext
    intro x
    calc
      f x = f (∏ i, coordinateHom i (x i)) := by
        rw [prod_coordinateHom]
      _ = ∏ i, f (coordinateHom i (x i)) := by
        rw [map_prod]
      _ = ∏ i, x i ^ n i := by
        apply Finset.prod_congr rfl
        intro i _hi
        have hi := congrArg
          (fun g : Circle →ₜ* Circle => g (x i)) (hn i)
        simpa [coordinateRestriction] using hi
      _ = torusCharacter n x := rfl
  · intro m hm
    funext i
    apply hn_unique i (m i)
    apply ContinuousMonoidHom.ext
    intro z
    have hz := congrArg
      (fun g : Torus d →ₜ* Circle => g (coordinateHom i z)) hm
    rw [torusCharacter_coordinateHom] at hz
    simpa [coordinateRestriction] using hz

theorem torusCharacter_injective :
    Function.Injective (torusCharacter : (d -> ℤ) -> Torus d →ₜ* Circle) := by
  intro m n h
  exact ((existsUnique_eq_torusCharacter (torusCharacter m)).unique
    (y₁ := n) (y₂ := m) h rfl).symm

/-- The finite-torus character group as an explicit equivalence of underlying
types with its integer lattice. -/
def integerLatticeEquivContinuousCharacter :
    (d -> ℤ) ≃ (Torus d →ₜ* Circle) :=
  Equiv.ofBijective torusCharacter
    ⟨torusCharacter_injective, fun f => by
      obtain ⟨n, hn⟩ := (existsUnique_eq_torusCharacter f).exists
      exact ⟨n, hn.symm⟩⟩

end
end CircleTorusCharacterLattice
end Math
