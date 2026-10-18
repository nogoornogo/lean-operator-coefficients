import Math.RepresentationTheory.Multiplicity.IsometricMultiplicity
import Mathlib.Tactic.NormNum

/-!
# Audits for isometric multiplicities and topological centralizer transport

The inputs include a genuinely non-isometric equivalence, repeated trivial
constituents, the zero space, and a nontrivial permutation action. All models
and isometries are constructed from the action, not supplied as certificates.
-/

namespace Math.AuditIsometricMultiplicity

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped MonoidAlgebra Math.IsometricMultiplicity

def scaling : ℂ ≃ₗ[ℂ] ℂ := LinearEquiv.smulOfNeZero ℂ ℂ 2 (by norm_num)

/-- The algebraic input to polar normalization need not already be isometric. -/
theorem scaling_not_isometry : ¬ Isometry scaling := by
  intro h
  have hn := h.dist_eq (1 : ℂ) 0
  norm_num [scaling, dist_eq_norm] at hn

theorem scaling_has_isometric_replacement :
    ∃ u : ℂ ≃ₗᵢ[ℂ] ℂ, ∀ (g : PUnit) x,
      u ((Representation.trivial ℂ PUnit ℂ) g x) =
        (Representation.trivial ℂ PUnit ℂ) g (u x) :=
  UnitaryIntertwiner.exists_isometric_intertwiner
    (rho := Representation.trivial ℂ PUnit ℂ)
    (sigma := Representation.trivial ℂ PUnit ℂ)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) scaling (fun _ _ => rfl)

def trivial (d : ℕ) : Representation ℂ PUnit (EuclideanSpace ℂ (Fin d)) :=
  Representation.trivial ℂ PUnit _

theorem trivial_unitary (d : ℕ) : UnitaryMultiplicity.IsUnitaryRepresentation (trivial d) :=
  fun _ _ _ => rfl

def trivialModel (d : ℕ) :=
  UnitaryMultiplicity.multiplicityModel (trivial d) (trivial_unitary d)

local instance trivialComponentsFintype (d : ℕ) :
    Fintype (isotypicComponents ℂ[PUnit] (trivial d).asModule) := by
  let := MultiplicityCommutant.finite_components (trivial d)
  exact Fintype.ofFinite _

set_option backward.isDefEq.respectTransparency false in
def trivialIsometry (d : ℕ) :
    EuclideanSpace ℂ (Fin d) ≃ₗᵢ[ℂ] IsometricMultiplicity.Space (trivial d) (trivialModel d) :=
  IsometricMultiplicity.isometricEquiv (trivial d) (trivialModel d) (trivial_unitary d)

example : Nonempty (EuclideanSpace ℂ (Fin 0) ≃ₗᵢ[ℂ]
    IsometricMultiplicity.Space (trivial 0) (trivialModel 0)) := ⟨trivialIsometry 0⟩

example : Nonempty (EuclideanSpace ℂ (Fin 2) ≃ₗᵢ[ℂ]
    IsometricMultiplicity.Space (trivial 2) (trivialModel 2)) := ⟨trivialIsometry 2⟩

def trivialUnitaryCentralizerEquiv (d : ℕ) :=
  IsometricMultiplicity.unitaryCentralizerEquiv
    (trivial d) (trivialModel d) (trivial_unitary d)

def trivialSpecialCentralizerEquiv (d : ℕ) :=
  IsometricMultiplicity.specialCentralizerEquiv
    (trivial d) (trivialModel d) (trivial_unitary d)

example : Continuous ⇑(UnitaryCentralizerTransport.unitaryConj
    (LinearIsometryEquiv.refl ℂ ℂ)) :=
  (UnitaryCentralizerTransport.unitaryConj (LinearIsometryEquiv.refl ℂ ℂ)).continuous

example : Continuous ⇑(UnitaryCentralizerTransport.unitaryConj
    (LinearIsometryEquiv.refl ℂ ℂ)).symm :=
  (UnitaryCentralizerTransport.unitaryConj (LinearIsometryEquiv.refl ℂ ℂ)).symm.continuous

example : IsTopologicalGroup (UnitaryCentralizerTransport.unitaryCentralizer (trivial 2)) :=
  inferInstance

example : IsTopologicalGroup (UnitaryCentralizerTransport.specialCentralizer (trivial 2)) :=
  inferInstance

/-- The natural permutation action, on a Hilbert rather than supremum-norm product. -/
def permutation : Representation ℂ (Equiv.Perm (Fin 2)) (EuclideanSpace ℂ (Fin 2)) where
  toFun g := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ g).toLinearMap
  map_one' := by ext x i; rfl
  map_mul' g h := by ext x i; rfl

theorem permutation_unitary : UnitaryMultiplicity.IsUnitaryRepresentation permutation :=
  fun g => (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ g).inner_map_map

theorem permutation_nontrivial : permutation (Equiv.swap 0 1) ≠ 1 := by
  intro h
  have hx := congrArg (fun T : Module.End ℂ (EuclideanSpace ℂ (Fin 2)) =>
    T (EuclideanSpace.single 0 1) 0) h
  norm_num [permutation, LinearIsometryEquiv.piLpCongrLeft_apply] at hx

def permutationModel := UnitaryMultiplicity.multiplicityModel permutation permutation_unitary

local instance permutationComponentsFintype :
    Fintype (isotypicComponents ℂ[Equiv.Perm (Fin 2)] permutation.asModule) := by
  let := MultiplicityCommutant.finite_components permutation
  exact Fintype.ofFinite _

set_option backward.isDefEq.respectTransparency false in
def permutationIsometry : EuclideanSpace ℂ (Fin 2) ≃ₗᵢ[ℂ]
    IsometricMultiplicity.Space permutation permutationModel :=
  IsometricMultiplicity.isometricEquiv permutation permutationModel permutation_unitary

theorem permutationIsometry_intertwines (g : Equiv.Perm (Fin 2))
    (x : EuclideanSpace ℂ (Fin 2)) :
    permutationIsometry (permutation g x) =
      IsometricMultiplicity.action permutation permutationModel g (permutationIsometry x) :=
  IsometricMultiplicity.isometricEquiv_intertwines permutation permutationModel
    permutation_unitary g x

def permutationSpecialCentralizerEquiv :=
  IsometricMultiplicity.specialCentralizerEquiv permutation permutationModel permutation_unitary

#print axioms UnitaryIntertwiner.adjoint_intertwines
#print axioms UnitaryIntertwiner.exists_isometric_intertwiner
#print axioms IsometricMultiplicity.algebraicEquiv
#print axioms IsometricMultiplicity.constituent_finrank_pos
#print axioms IsometricMultiplicity.finrank_eq_sum
#print axioms IsometricMultiplicity.isometricEquiv
#print axioms IsometricMultiplicity.isometricEquiv_intertwines
#print axioms UnitaryCentralizerTransport.det_unitaryConj
#print axioms IsometricMultiplicity.unitaryCentralizerEquiv
#print axioms IsometricMultiplicity.specialCentralizerEquiv
#print axioms scaling_not_isometry
#print axioms scaling_has_isometric_replacement
#print axioms trivialIsometry
#print axioms trivialSpecialCentralizerEquiv
#print axioms permutation_nontrivial
#print axioms permutationIsometry_intertwines
#print axioms permutationSpecialCentralizerEquiv

end

end Math.AuditIsometricMultiplicity
