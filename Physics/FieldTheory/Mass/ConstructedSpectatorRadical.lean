import Physics.FieldTheory.Mass.OrthogonalMass

/-! An explicit massive dual pair with exactly the declared light radical. -/
namespace GUT.ConstructedSpectatorRadical
set_option autoImplicit false
noncomputable section
open Representation InvariantWeylMass
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  (light : Representation ℂ G V) (spectator : Representation ℂ G W)

abbrev action := light.prod (spectator.prod spectator.dual)
def mass : SymmetricMass (action light spectator) :=
  OrthogonalMass.prod (SymmetricMass.zero light) (LightInheritanceBoundary.pairedMass spectator)

theorem mem_radical (x : V × (W × Module.Dual ℂ W)) :
    x ∈ (mass light spectator).radical.toSubmodule ↔ x.2 = 0 := by
  rw [mass, OrthogonalMass.mem_radical, LightInheritanceBoundary.paired_mem_radical_iff]
  simp [SymmetricMass.mem_radical,SymmetricMass.zero]

def radicalEquiv : Equiv (mass light spectator).radical.toRepresentation light :=
  .mk
    { toFun := fun x => x.val.1
      invFun := fun v => ⟨(v,0),(mem_radical light spectator _).mpr rfl⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact ((mem_radical light spectator _).mp x.property).symm
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (by intro g; rfl)
end
end GUT.ConstructedSpectatorRadical
