import Math.RepresentationTheory.Characters.CharacterRestriction

/-!
# Self-dual restricted characters

An actual equivariant self-duality, or conjugacy to inverse in the ambient
group, forces equality of a restricted character with its dual. The latter
condition may hold only on the subgroup being tested. No compactness,
unitarity, irreducible classification, or source weight model is needed.
-/

set_option autoImplicit false

namespace Math.SelfDualCharacter

noncomputable section

variable {G K k V : Type*} [Group G] [Group K] [Field k]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  (rho : Representation k G V)

theorem character_eq_inv_of_equiv (e : Representation.Equiv rho rho.dual) (g : G) :
    rho.character g = rho.character g⁻¹ := by
  rw [← Representation.char_dual]
  exact congrFun (Representation.char_iso e) g

theorem restrict_character_eq_dual_of_equiv (i : K →* G)
    (e : Representation.Equiv rho rho.dual) (g : K) :
    Representation.character (rho.comp i) g =
      Representation.character (Representation.dual (rho.comp i)) g := by
  rw [Representation.char_dual]
  change rho.character (i g) = rho.character (i g⁻¹)
  rw [map_inv]
  exact character_eq_inv_of_equiv rho e (i g)

/-- Conjugators may depend on the tested element. -/
theorem restrict_character_eq_dual_of_conjugate_inverse (i : K →* G)
    (hconj : ∀ g, ∃ n : G, i g⁻¹ = n * i g * n⁻¹) (g : K) :
    Representation.character (rho.comp i) g =
      Representation.character (Representation.dual (rho.comp i)) g := by
  rw [Representation.char_dual]
  change rho.character (i g) = rho.character (i g⁻¹)
  obtain ⟨n, hn⟩ := hconj g
  rw [hn, Representation.char_conj]

theorem restrict_character_eq_dual_of_inversion_element (i : K →* G) (n : G)
    (hconj : ∀ g, i g⁻¹ = n * i g * n⁻¹) (g : K) :
    Representation.character (rho.comp i) g =
      Representation.character (Representation.dual (rho.comp i)) g :=
  restrict_character_eq_dual_of_conjugate_inverse rho i (fun g => ⟨n, hconj g⟩) g

theorem virtualCharacter_restrict_inv
    {I : Type*} {W : I → Type*} [∀ i, AddCommGroup (W i)]
    [∀ i, Module k (W i)] [∀ i, FiniteDimensional k (W i)]
    (reps : ∀ i, Representation k G (W i)) (coeff : I →₀ ℤ)
    (i : K →* G) (hconj : ∀ g, ∃ n : G, i g⁻¹ = n * i g * n⁻¹) (g : K) :
    CharacterRestriction.virtualCharacter reps coeff (i g⁻¹) =
      CharacterRestriction.virtualCharacter reps coeff (i g) := by
  obtain ⟨n, hn⟩ := hconj g
  unfold CharacterRestriction.virtualCharacter Finsupp.sum
  apply Finset.sum_congr rfl
  intro j _
  simp only [hn, Representation.char_conj]

end

end Math.SelfDualCharacter
