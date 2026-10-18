import GUT.SU6.Characters.AmbientLaurent
import GUT.SU6.Characters.FifthMomentHypercharge
import GUT.SU6.Characters.VirtualRestriction

/-!
# Actual restricted characters in the ambient Laurent model

This module isolates the remaining representation-theory input from the
algebra that follows it.  An `ActualAmbientLaurentModel` supplies only a
canonical rank-five Laurent polynomial whose faithful evaluation is the
actual restricted trace character.  Full Weyl invariance is *not* a field of
the certificate: trace conjugacy, signed transposition representatives, and
faithfulness prove it automatically.

The same argument is closed under finite integer virtual combinations.  The
resulting invariant Laurent character maps injectively to the normalized
rational weight model used by the degree-five hypercharge obstruction.
-/

namespace GUT
namespace AmbientCharacterBridge

open AmbientWeightLattice

noncomputable section

abbrev SU6 := ActualRestriction.SU6
abbrev DiagonalPoint := AmbientLaurent.DiagonalPoint
abbrev Poly := AmbientLaurent.Poly

/-- A source-side Laurent realization of one actual restricted character.
The evaluator and its faithfulness are the concrete common constructions in
`AmbientLaurent`. -/
structure ActualAmbientLaurentModel
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ SU6 V) where
  poly : Poly
  evaluates_character :
    ∀ t : DiagonalPoint,
      AmbientLaurent.diagonalEval poly t =
        ActualRestriction.restrictedCharacter rho t

namespace ActualAmbientLaurentModel

theorem transposition_fixed
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {rho : Representation ℂ SU6 V}
    (M : ActualAmbientLaurentModel rho)
    (a b : I6) (h : a ≠ b) :
    AmbientWeightLattice.permuteCharacter
        (SignedWeylTransposition.transposition a b) M.poly = M.poly := by
  apply AmbientLaurent.diagonalEval_faithful
  intro t
  rw [AmbientLaurent.diagonalEval_permute_transposition a b h,
    M.evaluates_character, M.evaluates_character]
  exact AmbientLaurent.restrictedCharacter_swap_fixed rho a b h t

/-- Every actual restricted character admitting the normalized Laurent
realization is invariant under the full ambient Weyl group. -/
theorem isWeylInvariant
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {rho : Representation ℂ SU6 V}
    (M : ActualAmbientLaurentModel rho) :
    AmbientWeightLattice.IsWeylInvariant M.poly := by
  intro sigma
  refine Equiv.Perm.swap_induction_on sigma ?_ ?_
  · exact AmbientWeightLattice.permuteCharacter_one M.poly
  · intro tau a b h _htau
    rw [← AmbientWeightLattice.permuteCharacter_mul]
    rw [_htau]
    simpa [SignedWeylTransposition.transposition] using
      M.transposition_fixed a b h

theorem weightCharacter_isWeylInvariant
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {rho : Representation ℂ SU6 V}
    (M : ActualAmbientLaurentModel rho) :
    AmbientWeylMoment.IsWeylInvariant
      (AmbientWeightLattice.toWeightCharacter M.poly) :=
  AmbientWeightLattice.isWeylInvariant_toWeightCharacter M.isWeylInvariant

end ActualAmbientLaurentModel

abbrev ActualRepresentation := VirtualRestriction.ActualSU6Representation
abbrev VirtualSummand := VirtualRestriction.VirtualSummand
abbrev FiniteVirtualRepresentation :=
  VirtualRestriction.FiniteVirtualSU6Representation

def actualRestrictedCharacter
    (R : ActualRepresentation) (t : DiagonalPoint) : ℂ :=
  ActualRestriction.restrictedCharacter R.rho t

def summandRestrictedCharacter
    (s : VirtualSummand) (t : DiagonalPoint) : ℂ :=
  (s.coeff : ℂ) * actualRestrictedCharacter s.rep t

def finiteVirtualRestrictedCharacter :
    FiniteVirtualRepresentation -> DiagonalPoint -> ℂ
  | [], _ => 0
  | s :: ss, t =>
      summandRestrictedCharacter s t +
        finiteVirtualRestrictedCharacter ss t

theorem finiteVirtualRestrictedCharacter_transposition_fixed
    (chi : FiniteVirtualRepresentation)
    (a b : I6) (h : a ≠ b) (t : DiagonalPoint) :
    finiteVirtualRestrictedCharacter chi
        (AmbientLaurent.DiagonalPoint.swap a b h t) =
      finiteVirtualRestrictedCharacter chi t := by
  induction chi with
  | nil => rfl
  | cons s ss ih =>
      simp only [finiteVirtualRestrictedCharacter,
        summandRestrictedCharacter, actualRestrictedCharacter]
      rw [AmbientLaurent.restrictedCharacter_swap_fixed s.rep.rho a b h t,
        ih]

/-- A finite virtual source together with one common normalized Laurent
polynomial for its actual restricted character. -/
structure VirtualAmbientLaurentModel
    (chi : FiniteVirtualRepresentation) where
  poly : Poly
  evaluates_character :
    ∀ t : DiagonalPoint,
      AmbientLaurent.diagonalEval poly t =
        finiteVirtualRestrictedCharacter chi t

namespace VirtualAmbientLaurentModel

theorem transposition_fixed
    {chi : FiniteVirtualRepresentation}
    (M : VirtualAmbientLaurentModel chi)
    (a b : I6) (h : a ≠ b) :
    AmbientWeightLattice.permuteCharacter
        (SignedWeylTransposition.transposition a b) M.poly = M.poly := by
  apply AmbientLaurent.diagonalEval_faithful
  intro t
  rw [AmbientLaurent.diagonalEval_permute_transposition a b h,
    M.evaluates_character, M.evaluates_character]
  exact finiteVirtualRestrictedCharacter_transposition_fixed chi a b h t

theorem isWeylInvariant
    {chi : FiniteVirtualRepresentation}
    (M : VirtualAmbientLaurentModel chi) :
    AmbientWeightLattice.IsWeylInvariant M.poly := by
  intro sigma
  refine Equiv.Perm.swap_induction_on sigma ?_ ?_
  · exact AmbientWeightLattice.permuteCharacter_one M.poly
  · intro tau a b h _htau
    rw [← AmbientWeightLattice.permuteCharacter_mul]
    rw [_htau]
    simpa [SignedWeylTransposition.transposition] using
      M.transposition_fixed a b h

theorem weightCharacter_isWeylInvariant
    {chi : FiniteVirtualRepresentation}
    (M : VirtualAmbientLaurentModel chi) :
    AmbientWeylMoment.IsWeylInvariant
      (AmbientWeightLattice.toWeightCharacter M.poly) :=
  AmbientWeightLattice.isWeylInvariant_toWeightCharacter M.isWeylInvariant

end VirtualAmbientLaurentModel

/-- A heterogeneous virtual summand carrying the actual Laurent realization
which torus weight theory must construct. -/
structure ModeledVirtualSummand where
  coeff : ℤ
  rep : ActualRepresentation
  poly : Poly
  evaluates_rep :
    ∀ t : DiagonalPoint,
      AmbientLaurent.diagonalEval poly t =
        actualRestrictedCharacter rep t

namespace ModeledVirtualSummand

def toVirtualSummand (s : ModeledVirtualSummand) : VirtualSummand :=
  { coeff := s.coeff, rep := s.rep }

def weightedPoly (s : ModeledVirtualSummand) : Poly :=
  AmbientLaurent.zscale s.coeff s.poly

theorem weightedPoly_evaluates
    (s : ModeledVirtualSummand) (t : DiagonalPoint) :
    AmbientLaurent.diagonalEval s.weightedPoly t =
      summandRestrictedCharacter s.toVirtualSummand t := by
  rw [weightedPoly]
  change
    AmbientLaurent.eval (AmbientLaurent.zscale s.coeff s.poly)
        t.toTorusVec =
      (s.coeff : ℂ) * actualRestrictedCharacter s.rep t
  rw [AmbientLaurent.eval_zscale]
  change
    (s.coeff : ℂ) * AmbientLaurent.diagonalEval s.poly t =
      (s.coeff : ℂ) * actualRestrictedCharacter s.rep t
  rw [s.evaluates_rep]

end ModeledVirtualSummand

abbrev ModeledFiniteVirtualRepresentation := List ModeledVirtualSummand

namespace ModeledFiniteVirtualRepresentation

def toVirtual :
    ModeledFiniteVirtualRepresentation -> FiniteVirtualRepresentation
  | [] => []
  | s :: ss => s.toVirtualSummand :: toVirtual ss

def poly : ModeledFiniteVirtualRepresentation -> Poly
  | [] => 0
  | s :: ss => s.weightedPoly + poly ss

theorem poly_evaluates
    (chi : ModeledFiniteVirtualRepresentation) (t : DiagonalPoint) :
    AmbientLaurent.diagonalEval (poly chi) t =
      finiteVirtualRestrictedCharacter (toVirtual chi) t := by
  induction chi with
  | nil => simp [poly, toVirtual, AmbientLaurent.diagonalEval,
      AmbientLaurent.eval_zero, finiteVirtualRestrictedCharacter]
  | cons s ss ih =>
      rw [poly, toVirtual, finiteVirtualRestrictedCharacter,
        AmbientLaurent.diagonalEval, AmbientLaurent.eval_add]
      change
        AmbientLaurent.diagonalEval s.weightedPoly t +
            AmbientLaurent.diagonalEval (poly ss) t =
          summandRestrictedCharacter s.toVirtualSummand t +
            finiteVirtualRestrictedCharacter (toVirtual ss) t
      rw [s.weightedPoly_evaluates, ih]

def toVirtualAmbientLaurentModel
    (chi : ModeledFiniteVirtualRepresentation) :
    VirtualAmbientLaurentModel (toVirtual chi) where
  poly := poly chi
  evaluates_character := poly_evaluates chi

theorem poly_isWeylInvariant
    (chi : ModeledFiniteVirtualRepresentation) :
    AmbientWeightLattice.IsWeylInvariant (poly chi) :=
  (toVirtualAmbientLaurentModel chi).isWeylInvariant

end ModeledFiniteVirtualRepresentation

/-- The exact physical fifth-moment compatibility condition on an ambient
Laurent character. -/
def HasSMFifthMoment
    (generations m n : ℚ) (p : Poly) : Prop :=
  ∀ a b t h : ℚ,
    generations * FifthMomentHypercharge.smFifthMoment a b t h =
      AmbientWeightLattice.fifthMomentValue p
        (FifthMomentHypercharge.ambientCartanCoordinates m n a b t h)

theorem hasAmbientWeylWeightCharacterSource
    (generations m n : ℚ) (p : Poly)
    (hWeyl : AmbientWeightLattice.IsWeylInvariant p)
    (hMoment : HasSMFifthMoment generations m n p) :
    FifthMomentHypercharge.HasAmbientWeylWeightCharacterSource
      generations m n := by
  refine ⟨AmbientWeightLattice.toWeightCharacter p,
    AmbientWeightLattice.isWeylInvariant_toWeightCharacter hWeyl, ?_⟩
  intro a b t h
  rw [AmbientWeightLattice.fifthMomentValue_toWeightCharacter]
  exact hMoment a b t h

theorem eq_standard_of_actualModel_fifthMoment
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {rho : Representation ℂ SU6 V}
    (M : ActualAmbientLaurentModel rho)
    (generations m n : ℚ) (hGenerations : generations ≠ 0)
    (hMoment : HasSMFifthMoment generations m n M.poly) :
    m = -2 ∧ n = 3 := by
  apply FifthMomentHypercharge.eq_standard_of_ambientWeylWeightCharacterSource
    generations m n hGenerations
  exact hasAmbientWeylWeightCharacterSource
    generations m n M.poly M.isWeylInvariant hMoment

theorem eq_standard_of_virtualModel_fifthMoment
    {chi : FiniteVirtualRepresentation}
    (M : VirtualAmbientLaurentModel chi)
    (generations m n : ℚ) (hGenerations : generations ≠ 0)
    (hMoment : HasSMFifthMoment generations m n M.poly) :
    m = -2 ∧ n = 3 := by
  apply FifthMomentHypercharge.eq_standard_of_ambientWeylWeightCharacterSource
    generations m n hGenerations
  exact hasAmbientWeylWeightCharacterSource
    generations m n M.poly M.isWeylInvariant hMoment

end
end AmbientCharacterBridge
end GUT
