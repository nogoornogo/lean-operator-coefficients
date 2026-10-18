import Math.RepresentationTheory.Characters.CharacterRestriction
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.NormNum

/-!
# Persistent audit of the general character restriction obstruction

The non-Abelian group of permutations of three points gives an obstruction
unrelated to SU(6). A signed combination of trivial representations supplies
a positive control. A nonfaithful evaluator demonstrates why faithfulness
cannot be omitted from the target-model theorem.
-/

namespace Math.AuditCharacterRestriction

open CharacterRestriction

noncomputable section

abbrev Perm3 := Equiv.Perm (Fin 3)

def conjugator : Perm3 := Equiv.swap 1 2

def action (g : Perm3) : Perm3 := conjugator * g * conjugator⁻¹

def target (g : Perm3) : ℚ := if g = Equiv.swap 0 1 then 1 else 0

theorem target_not_invariant :
    target (action (Equiv.swap 0 1)) ≠ target (Equiv.swap 0 1) := by
  decide

/-- No finite integer combination from any family of actual rational
representations realizes this target, even on the whole group. -/
theorem target_not_virtualCharacter
    {I : Type*} {V : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)]
    [∀ i, FiniteDimensional ℚ (V i)]
    (rho : ∀ i, Representation ℚ Perm3 (V i)) :
    target ∉ Set.range (fun coeff : I →₀ ℤ => virtualCharacter rho coeff ∘ id) :=
  not_mem_virtualRestrictionImage rho id action conjugator (fun _ => rfl)
    target (fun h => target_not_invariant (h (Equiv.swap 0 1)))

def trivialFamily (_ : Fin 2) : Representation ℚ Perm3 ℚ :=
  Representation.trivial ℚ Perm3 ℚ

def signedCoefficients : Fin 2 →₀ ℤ :=
  Finsupp.single 0 2 + Finsupp.single 1 (-1)

/-- Signed coefficients are allowed, and realizable targets are not excluded. -/
theorem signed_trivial_character (g : Perm3) :
    virtualCharacter trivialFamily signedCoefficients g = 1 := by
  rw [signedCoefficients, virtualCharacter_add,
    virtualCharacter_single, virtualCharacter_single]
  norm_num [trivialFamily, Representation.character, Representation.trivial]

theorem constant_one_in_image :
    (fun _ : Perm3 => (1 : ℚ)) ∈ Set.range (virtualCharacter trivialFamily) :=
  ⟨signedCoefficients, funext signed_trivial_character⟩

/-- The group-parameter map need not be injective. -/
example {I : Type*} {V : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)]
    [∀ i, FiniteDimensional ℚ (V i)]
    (rho : ∀ i, Representation ℚ Perm3 (V i)) :
    (fun t : Bool => if t then (1 : ℚ) else 0) ∉
      Set.range (fun coeff : I →₀ ℤ => virtualCharacter rho coeff ∘ fun _ : Bool => 1) := by
  apply not_mem_virtualRestrictionImage rho (fun _ : Bool => 1) Bool.not 1
    (by intro t; simp)
  intro h
  have hfalse := h false
  norm_num at hfalse

/-- A nonfixed model can evaluate to a realizable invariant function if
the evaluator is not faithful. This prevents dropping that hypothesis. -/
theorem nonfaithful_evaluation_counterexample :
    let eval : Bool → Perm3 → ℚ := fun _ _ => 1
    (∀ p g, eval (Bool.not p) g = eval p (action g)) ∧
      Bool.not false ≠ false ∧
      eval false ∈ Set.range (virtualCharacter trivialFamily) ∧
      ¬ Function.Injective eval := by
  refine ⟨fun _ _ => rfl, by decide, constant_one_in_image, ?_⟩
  intro h
  have : (false : Bool) = true := h rfl
  cases this

#print axioms CharacterRestriction.character_restriction_invariant
#print axioms CharacterRestriction.virtualCharacter_restriction_invariant
#print axioms CharacterRestriction.not_mem_virtualRestrictionImage
#print axioms CharacterRestriction.not_mem_finiteVirtualRestrictionImage
#print axioms CharacterRestriction.not_mem_virtualRestrictionImage_of_nonfixed_model
#print axioms CharacterRestriction.not_mem_range_of_nonfixed_model
#print axioms target_not_virtualCharacter
#print axioms constant_one_in_image
#print axioms nonfaithful_evaluation_counterexample

end

end Math.AuditCharacterRestriction
