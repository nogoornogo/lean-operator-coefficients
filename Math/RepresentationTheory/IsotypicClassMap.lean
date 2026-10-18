import TauCeti.RingTheory.Semisimple.RegularIsotypicComponent

/-! Universe-safe labels for the distinct isotypic components of an arbitrary module. -/
namespace Math.IsotypicClassMap
set_option autoImplicit false
noncomputable section
variable {R M : Type*} [Ring R] [IsSemisimpleRing R]
  [AddCommGroup M] [Module R M]

def simpleClassMap : TauCeti.SimpleSubmoduleClasses R M →
    TauCeti.SimpleSubmoduleClasses R R :=
  TauCeti.SimpleSubmoduleClasses.lift (fun N _ => TauCeti.simpleModuleClass R N)
    (fun _ _ _ _ e => TauCeti.simpleModuleClass_eq_iff.mpr e)

theorem simpleClassMap_injective : Function.Injective (simpleClassMap (R := R) (M := M)) := by
  intro c d
  induction c using TauCeti.SimpleSubmoduleClasses.ind with
  | mk N hN =>
    induction d using TauCeti.SimpleSubmoduleClasses.ind with
    | mk N' hN' =>
      intro h
      change TauCeti.simpleModuleClass R N = TauCeti.simpleModuleClass R N' at h
      exact TauCeti.SimpleSubmoduleClasses.mk_eq_mk_iff.mpr
        (TauCeti.simpleModuleClass_eq_iff.mp h)

def componentClass (c : isotypicComponents R M) : TauCeti.SimpleSubmoduleClasses R R :=
  simpleClassMap ((TauCeti.simpleSubmoduleClassesEquiv R M).symm c)

theorem componentClass_injective : Function.Injective (componentClass (R := R) (M := M)) :=
  simpleClassMap_injective.comp (TauCeti.simpleSubmoduleClassesEquiv R M).symm.injective

@[simp] theorem componentClass_simple (N : Submodule R M) [IsSimpleModule R N] :
    componentClass (⟨isotypicComponent R M N, N, inferInstance, rfl⟩) =
      TauCeti.simpleModuleClass R N := by
  have he : (⟨isotypicComponent R M N, N, inferInstance, rfl⟩ : isotypicComponents R M) =
      TauCeti.simpleSubmoduleClassesEquiv R M (TauCeti.SimpleSubmoduleClasses.mk N) := by
    apply Subtype.ext
    exact (TauCeti.coe_simpleSubmoduleClassesEquiv_mk N).symm
  rw [he, componentClass, Equiv.symm_apply_apply]
  exact TauCeti.SimpleSubmoduleClasses.lift_mk N

end
end Math.IsotypicClassMap
