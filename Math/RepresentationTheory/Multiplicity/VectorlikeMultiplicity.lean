import Math.RepresentationTheory.Multiplicity.MultiplicityDuality
import Math.RepresentationTheory.Multiplicity.MultiplicityTransport
import Math.RepresentationTheory.Multiplicity.BalancedMultiplicityExtension

/-! A full vectorlike summand supplies the balanced multiplicity certificate.
Duality acts on both factors of the product group. -/

namespace Math.VectorlikeMultiplicity
noncomputable section
open Representation ProductFactorization SplitRepresentationProjection

variable {G H V U : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
  (x : Representation ℂ (G × H) V) (r : Representation ℂ G U)

def prodComm {A B : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (a : Representation ℂ H A) (b : Representation ℂ H B) :
    Equiv (a.prod b) (b.prod a) where
  toLinearEquiv := LinearEquiv.prodComm ℂ A B
  isIntertwining' h := by ext v <;> rfl

variable [IsIrreducible r] [IsIrreducible r.dual]

def dualOther (hs : IsSemisimpleRepresentation (firstRestriction x)) :
    Equiv (multiplicityRepresentation x.dual r) (multiplicityRepresentation x r.dual).dual :=
  (MultiplicityTransport.source x.dual (bidualEquiv r)).trans
    (MultiplicityDuality.equiv x r.dual hs)

def balance (hs : IsSemisimpleRepresentation (firstRestriction x)) :
    Equiv (multiplicityRepresentation (x.prod x.dual) r.dual).dual
      (multiplicityRepresentation (x.prod x.dual) r) :=
  (dualEquiv (MultiplicityTransport.prod x x.dual r.dual)).trans
    ((dualProdEquiv _ _).symm.trans
      ((prodEquiv (dualOther x r hs).symm
        ((dualEquiv (MultiplicityDuality.equiv x r hs)).trans (bidualEquiv _).symm)).trans
        ((prodComm _ _).trans (MultiplicityTransport.prod x x.dual r).symm)))

section Coordinates
variable {Z : Type*} [AddCommGroup Z] [Module ℂ Z] [FiniteDimensional ℂ Z]
  (z : Representation ℂ H Z)

def coordinateAction : Representation ℂ H (Fin (Module.finrank ℂ Z) → ℂ) where
  toFun h := (Module.finBasis ℂ Z).equivFun.conj (z h)
  map_one' := by
    rw [map_one]
    exact (Module.finBasis ℂ Z).equivFun.conjRingEquiv.map_one
  map_mul' g h := by
    rw [map_mul]
    exact (Module.finBasis ℂ Z).equivFun.conjRingEquiv.map_mul _ _

def coordinateEquiv : Equiv z (coordinateAction z) where
  toLinearEquiv := (Module.finBasis ℂ Z).equivFun
  isIntertwining' h := by ext v; simp [coordinateAction]
end Coordinates

section Extension
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  (tau : Representation ℂ (G × H) E) (base : Representation ℂ (G × H) F)
  (e : Equiv tau (base.prod (x.prod x.dual)))

def extension (hs : IsSemisimpleRepresentation (firstRestriction x)) :
    BalancedMultiplicityExtension.Extension tau base r where
  dimension := Module.finrank ℂ (MultiplicitySpace (x.prod x.dual) r)
  extra := coordinateAction (multiplicityRepresentation (x.prod x.dual) r)
  positive := (MultiplicityTransport.target e r).trans
    ((MultiplicityTransport.prod base (x.prod x.dual) r).trans
      (prodEquiv (Representation.Equiv.refl _) (coordinateEquiv _)))
  negative := (dualEquiv (MultiplicityTransport.target e r.dual)).trans
    ((dualEquiv (MultiplicityTransport.prod base (x.prod x.dual) r.dual)).trans
      ((dualProdEquiv _ _).symm.trans
        (prodEquiv (Representation.Equiv.refl _) ((balance x r hs).trans (coordinateEquiv _)))))

end Extension
end
end Math.VectorlikeMultiplicity
