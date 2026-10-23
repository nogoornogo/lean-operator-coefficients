import Physics.FieldTheory.Mass.Algebra.InvariantWeylMass

/-! An equivariant inclusion and agreement of restricted masses do not
preserve light fields: pairing a representation with its dual lifts them. -/
set_option autoImplicit false
namespace Physics.LightInheritanceBoundary
noncomputable section
open InvariantWeylMass

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  (rho : Representation ℂ G V)

def pairedMass : SymmetricMass (rho.prod rho.dual) :=
  ofDirac (Representation.IntertwiningMap.id rho)

def retained : Representation.IntertwiningMap rho (rho.prod rho.dual) :=
  Representation.IntertwiningMap.inl ℂ rho rho.dual

theorem retained_injective : Function.Injective (retained rho) := by
  intro x y h
  exact congrArg Prod.fst h

theorem restricted_mass_eq (x y : V) :
    (pairedMass rho).form (retained rho x) (retained rho y) =
      (SymmetricMass.zero rho).form x y := by
  change (0 : Module.Dual ℂ V) x + (0 : Module.Dual ℂ V) y = 0
  simp

theorem paired_mem_radical_iff (x : V × Module.Dual ℂ V) :
    x ∈ (pairedMass rho).radical.toSubmodule ↔ x = 0 := by
  change x ∈ DiracWeylConvention.radical (LinearMap.id : V →ₗ[ℂ] V) ↔ _
  rw [DiracWeylConvention.mem_radical_iff]
  constructor
  · rintro ⟨hx, hphi⟩
    apply Prod.ext
    · exact hx
    · exact LinearMap.ext hphi
  · rintro rfl
    simp

theorem paired_radical_eq_bot : (pairedMass rho).radical.toSubmodule = ⊥ := by
  ext x
  simpa only [Submodule.mem_bot] using paired_mem_radical_iff rho x

theorem light_not_preserved (x : V) (hx : x ≠ 0) :
    x ∈ (SymmetricMass.zero rho).radical.toSubmodule ∧
      retained rho x ∉ (pairedMass rho).radical.toSubmodule := by
  constructor
  · rw [SymmetricMass.mem_radical]
    intro y
    rfl
  · rw [paired_mem_radical_iff]
    intro h
    exact hx (congrArg Prod.fst h)

end
end Physics.LightInheritanceBoundary
