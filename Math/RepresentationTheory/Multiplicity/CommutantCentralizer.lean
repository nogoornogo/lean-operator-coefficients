import Math.RepresentationTheory.Multiplicity.MultiplicityCommutant
import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.Commute.Units

/-!
# From the intertwiner algebra to the general-linear centralizer

The equivalences concern the actual operators commuting with the action,
not an independently defined abstract group. No unitary claim is made.
-/

namespace Math.CommutantCentralizer

noncomputable section

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
  (rho : Representation k G V)

/-- Operators commuting with the representation, as a subalgebra. -/
abbrev commutant := Subalgebra.centralizer k (Set.range rho)

/-- The centralizer subalgebra and self-intertwiners have the same operators. -/
def commutantEquivIntertwiner : commutant rho ≃ₐ[k] rho.IntertwiningMap rho where
  toFun f := ⟨f.1, fun g => (f.2 _ ⟨g, rfl⟩).symm⟩
  invFun f := ⟨f.toLinearMap, by
    rintro _ ⟨g, rfl⟩
    exact (f.isIntertwining' g).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The invertible operators commuting with the action. -/
def linearCentralizer : Subgroup (Module.End k V)ˣ :=
  (commutant rho).toSubmonoid.units

theorem mem_linearCentralizer_iff (u : (Module.End k V)ˣ) :
    u ∈ linearCentralizer rho ↔ ∀ g, rho g * (u : Module.End k V) = u * rho g := by
  constructor
  · intro h g
    exact h.1 _ ⟨g, rfl⟩
  · intro h
    constructor
    · rintro _ ⟨g, rfl⟩
      exact h g
    · rintro _ ⟨g, rfl⟩
      exact (show Commute (rho g) (u : Module.End k V) from h g).units_inv_right

/-- A group isomorphism, retaining the actual operator centralizer as source. -/
def linearCentralizerEquivUnits :
    linearCentralizer rho ≃* (rho.IntertwiningMap rho)ˣ :=
  (commutant rho).toSubmonoid.unitsEquivUnitsType.trans
    (Units.mapEquiv (commutantEquivIntertwiner rho).toMulEquiv)

open scoped MonoidAlgebra

/-- Multiplicity matrices classify the full general-linear centralizer. -/
def linearCentralizerEquiv [IsAlgClosed k] [FiniteDimensional k V]
    (h : Representation.IsSemisimpleRepresentation rho)
    (D : MultiplicityCommutant.Model k[G] rho.asModule) :
    linearCentralizer rho ≃*
      Π c : isotypicComponents k[G] rho.asModule,
        (Matrix (Fin (D.multiplicity c)) (Fin (D.multiplicity c)) k)ˣ :=
  (linearCentralizerEquivUnits rho).trans
    (MultiplicityCommutant.automorphismEquiv rho h D)

end

section Group

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (rho : Representation k G V)

/-- For a group action this is the ordinary subgroup centralizer in `GL(V)`. -/
theorem linearCentralizer_eq_groupCentralizer :
    linearCentralizer rho = Subgroup.centralizer (Set.range rho.asGroupHom) := by
  ext u
  rw [mem_linearCentralizer_iff, Subgroup.mem_centralizer_iff]
  simp only [Set.forall_mem_range]
  constructor
  · intro h g
    apply Units.ext
    exact h g
  · intro h g
    exact congrArg Units.val (h g)

end Group

end Math.CommutantCentralizer
