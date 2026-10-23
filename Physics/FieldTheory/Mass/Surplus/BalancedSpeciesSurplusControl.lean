import Physics.FieldTheory.Mass.Surplus.SpeciesSurplusNecessity

namespace Physics.BalancedSpeciesSurplusControl
set_option autoImplicit false
noncomputable section
open Math Representation StandardSMGaugeTensor InvariantWeylMass
open PhysicalCommonCopyModel PhysicalSpeciesCopySurplus SplitRepresentationProjection
open ExternalInvariantTensor
open scoped TensorProduct
variable {H S : Type*} [Group H] [AddCommGroup S] [Module ℂ S]
  [FiniteDimensional ℂ S] [Nontrivial S] (s : Representation ℂ H S)

abbrev qAction := external quark s
abbrev uAction := external upRight.dual s
abbrev eAction := external electronRight.dual s
abbrev Field := (Quark ⊗[ℂ] S) × ((Module.Dual ℂ SMEpsilonTensor.Color ⊗[ℂ] S) ×
  (Module.Dual ℂ ℂ ⊗[ℂ] S))
local instance : AddCommGroup (Field (S := S)) := inferInstance
def fields : Representation ℂ (GaugeGroup × H) (Field (S := S)) := (qAction s).prod ((uAction s).prod (eAction s))
def mass : SymmetricMass (fields s) := SymmetricMass.zero (fields s)

/-- Zero mass is an actual symmetric invariant mass with proved species squares. -/
def zeroSpecies {F V : Type*} [AddCommGroup F] [Module ℂ F]
    [AddCommGroup V] [Module ℂ V] (rho : Representation ℂ (GaugeGroup × H) F)
    (r : Representation ℂ GaugeGroup V)
    (i : IntertwiningMap (external r s) rho) (hi : Function.Injective i) :
    Species (s := s) (t := s) r (SymmetricMass.zero rho) where
  map := 0
  embed := i
  injective := hi
  dualField := 0
  mass_square := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    rfl

def realization : PhysicalSpeciesCopySurplus.Realization
    (aq := s) (cq := s) (au := s) (cu := s) (ae := s) (ce := s) (mass s) where
  q := zeroSpecies s (fields s) quark
    (IntertwiningMap.inl ℂ (qAction s) ((uAction s).prod (eAction s)))
    (by intro x y h; exact congrArg Prod.fst h)
  u := zeroSpecies s (fields s) upRight.dual
    ((IntertwiningMap.inr ℂ (qAction s) ((uAction s).prod (eAction s))).comp
      (IntertwiningMap.inl ℂ (uAction s) (eAction s)))
    (by intro x y h; exact congrArg (fun z => z.2.1) h)
  e := zeroSpecies s (fields s) electronRight.dual
    ((IntertwiningMap.inr ℂ (qAction s) ((uAction s).prod (eAction s))).comp
      (IntertwiningMap.inr ℂ (uAction s) (eAction s)))
    (by intro x y h; exact congrArg (fun z => z.2.2) h)

def zeroKernelSplit : Split (0 : IntertwiningMap s s).ker.toRepresentation s where
  project := CharacterExact.subtypeIntertwiner (0 : IntertwiningMap s s).ker
  embed :=
    { toLinearMap :=
        { toFun := fun x => ⟨x, by change (0 : IntertwiningMap s s) x = 0; rfl⟩
          map_add' := by intro x y; rfl
          map_smul' := by intro c x; rfl }
      isIntertwining' g := by apply LinearMap.ext; intro x; rfl }
  left_inv _ := rfl

theorem physical_light_coefficient : (realization s).HasLightExterior := by
  refine ⟨(realization s).q.range_light, (realization s).u.range_light,
    (realization s).e.range_light, ?_⟩
  apply PhysicalQqueEndpoint.of_alternation
  exact QqueSpinorExterior.exists_on_fields (zeroKernelSplit s) (zeroKernelSplit s)
    (zeroKernelSplit s) _ _ _ (realization s).quarkEq
    (realization s).upEq (realization s).electronEq

variable {R : Type*} [AddCommGroup R] [Module ℂ R] [FiniteDimensional ℂ R]
omit [Nontrivial S] [FiniteDimensional ℂ S] [FiniteDimensional ℂ R] in
theorem no_surplus (r : Representation ℂ H R) : ¬ SpeciesCopySurplus.Surplus r s s := by
  unfold SpeciesCopySurplus.Surplus
  exact lt_irrefl _

theorem not_forbidden : ¬ SpeciesSurplusNecessity.ForbiddenExterior (realization s) := by
  intro h
  obtain ⟨c,hc⟩ := (physical_light_coefficient s).2.2.2
  exact hc (h c)

omit [FiniteDimensional ℂ R] in
theorem converse_counterexample (r : Representation ℂ H R) :
    ¬ (SpeciesCopySurplus.Surplus r s s ∧ SpeciesCopySurplus.Surplus r s s ∧
      SpeciesCopySurplus.Surplus r s s) ∧
    ¬ SpeciesSurplusNecessity.ForbiddenExterior (realization s) :=
  ⟨fun h => no_surplus s r h.1,not_forbidden s⟩
end
end Physics.BalancedSpeciesSurplusControl
