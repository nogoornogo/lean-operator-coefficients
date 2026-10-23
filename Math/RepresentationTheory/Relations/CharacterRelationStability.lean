import Math.RepresentationTheory.Relations.FiniteStatisticsQuotient
import Mathlib.Tactic.Module

/-! Character exchange relations are stable under the full statistics action.
This is derived from the group law, not an additional application assumption. -/
namespace Math.CharacterRelationStability
set_option autoImplicit false
noncomputable section
open Representation
variable {k H S U : Type*} [Field k] [Group H] [Group S]
  [AddCommGroup U] [Module k U]
  (rho : Representation k H U) (b : Representation k S U)
  (commutes : ∀ g h u, b g (rho h u) = rho h (b g u))
  (chi : S →* kˣ)

abbrev exchange := FiniteStatisticsQuotient.exchange rho b commutes
abbrev relation := SignedRelationQuotient.relation rho (exchange rho b commutes)
  (fun s => (chi s).val)
abbrev relations := SignedRelationQuotient.relations rho (exchange rho b commutes)
  (fun s => (chi s).val)

theorem relation_mem (s : S) (u : U) :
    relation rho b commutes chi s u ∈ relations rho b commutes chi :=
  Submodule.subset_span ⟨(s, u), rfl⟩

theorem action_relation (g s : S) (u : U) :
    b g (relation rho b commutes chi s u) =
      relation rho b commutes chi (g * s) u -
        (chi s).val • relation rho b commutes chi g u := by
  simp only [relation, exchange, SignedRelationQuotient.relation,
    FiniteStatisticsQuotient.exchange, map_sub, map_smul, map_mul,
    Units.val_mul]
  module

theorem stable : ∀ g, relations rho b commutes chi ≤
    (relations rho b commutes chi).comap (b g) := by
  apply RelationQuotient.relations_stable
  intro g su
  change b g (relation rho b commutes chi su.1 su.2) ∈ _
  rw [action_relation]
  exact Submodule.sub_mem _ (relation_mem rho b commutes chi (g * su.1) su.2)
    (Submodule.smul_mem _ _ (relation_mem rho b commutes chi g su.2))

end
end Math.CharacterRelationStability
