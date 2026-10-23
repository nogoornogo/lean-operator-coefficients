import Physics.FieldTheory.Mass.Spectrum.EquivariantMassIndex
import Mathlib.Analysis.InnerProductSpace.ProdL2

open Math

/-!
# Realizing finite unitary virtual representations by a signed pair

Every finite virtual representation whose summands carry invariant Hermitian
inner products can be written as the difference of two actual
finite-dimensional unitary representations.  Integer coefficients are split
into their positive and negative parts, and repeated summands are assembled
using the Hilbert-space `L2` product.

This supplies a canonical ultraviolet source and target for an equivariant
mass map; its source-minus-target character is the original virtual
character.
-/

namespace Physics
namespace UnitaryVirtualRealization

open CompactEmbeddingClassification
open EquivariantMassIndex
open PhysicalRestrictionBridge

noncomputable section

universe u

/-- A finite-dimensional group representation together with an invariant
positive-definite Hermitian inner product. -/
structure ActualUnitaryGroupRepresentation (G : Type u) [Group G] where
  V : Type
  [normedAddCommGroup : NormedAddCommGroup V]
  [innerProductSpace : InnerProductSpace ℂ V]
  [finiteDimensional : FiniteDimensional ℂ V]
  rho : Representation ℂ G V
  unitary : IsUnitaryRepresentation rho

attribute [instance]
  ActualUnitaryGroupRepresentation.normedAddCommGroup
  ActualUnitaryGroupRepresentation.innerProductSpace
  ActualUnitaryGroupRepresentation.finiteDimensional

namespace ActualUnitaryGroupRepresentation

variable {G : Type u} [Group G]

def toActualGroupRepresentation (R : ActualUnitaryGroupRepresentation G) :
    ActualGroupRepresentation G where
  V := R.V
  rho := R.rho

/-- Transport the ordinary product representation to the `L2` product, whose
norm is induced by the sum Hermitian inner product. -/
def productRepresentation (R S : ActualUnitaryGroupRepresentation G) :
    Representation ℂ G (WithLp 2 (R.V × S.V)) where
  toFun g :=
    (WithLp.linearEquiv 2 ℂ (R.V × S.V)).symm.conj
      ((R.rho.prod S.rho) g)
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp

/-- The transported `L2` product representation is equivalent to the raw
algebraic product representation. -/
def productEquiv (R S : ActualUnitaryGroupRepresentation G) :
    Representation.Equiv (productRepresentation R S) (R.rho.prod S.rho) :=
  Representation.Equiv.mk (WithLp.linearEquiv 2 ℂ (R.V × S.V)) (by
    intro g
    apply LinearMap.ext
    intro x
    simp [productRepresentation])

/-- Orthogonal products of unitary representations remain unitary. -/
theorem productRepresentation_unitary
    (R S : ActualUnitaryGroupRepresentation G) :
    IsUnitaryRepresentation (productRepresentation R S) := by
  intro g x y
  change
    inner ℂ (R.rho g (WithLp.ofLp x).1) (R.rho g (WithLp.ofLp y).1) +
        inner ℂ (S.rho g (WithLp.ofLp x).2) (S.rho g (WithLp.ofLp y).2) =
      inner ℂ (WithLp.ofLp x).1 (WithLp.ofLp y).1 +
        inner ℂ (WithLp.ofLp x).2 (WithLp.ofLp y).2
  rw [R.unitary, S.unitary]

/-- Orthogonal product in the bundled unitary interface. -/
def product (R S : ActualUnitaryGroupRepresentation G) :
    ActualUnitaryGroupRepresentation G where
  V := WithLp 2 (R.V × S.V)
  rho := productRepresentation R S
  unitary := productRepresentation_unitary R S

theorem product_character (R S : ActualUnitaryGroupRepresentation G) (g : G) :
    (product R S).rho.character g =
      R.rho.character g + S.rho.character g := by
  calc
    (product R S).rho.character g =
        (R.rho.prod S.rho).character g :=
      congrFun (Representation.char_iso (productEquiv R S)) g
    _ = R.rho.character g + S.rho.character g :=
      LinearMap.trace_prodMap' (R.rho g) (S.rho g)

/-- The zero-dimensional unitary representation. -/
def zero : ActualUnitaryGroupRepresentation G where
  V := EuclideanSpace ℂ (Fin 0)
  rho := Representation.trivial ℂ G (EuclideanSpace ℂ (Fin 0))
  unitary := by
    intro g x y
    rfl

@[simp]
theorem zero_character (g : G) : zero.rho.character g = 0 := by
  change LinearMap.trace ℂ (EuclideanSpace ℂ (Fin 0)) LinearMap.id = 0
  rw [LinearMap.trace_id, finrank_euclideanSpace_fin]
  norm_num

/-- `n` orthogonal copies of one unitary representation. -/
def copies : ℕ → ActualUnitaryGroupRepresentation G →
    ActualUnitaryGroupRepresentation G
  | 0, _ => zero
  | n + 1, R => product R (copies n R)

theorem copies_character (n : ℕ) (R : ActualUnitaryGroupRepresentation G)
    (g : G) :
    (copies n R).rho.character g = (n : ℂ) * R.rho.character g := by
  induction n with
  | zero =>
      rw [copies, zero_character]
      norm_num
  | succ n ih =>
      rw [copies, product_character, ih]
      push_cast
      ring

end ActualUnitaryGroupRepresentation

/-- One integer-weighted summand with a chosen unitary model. -/
structure UnitaryVirtualSummand (G : Type u) [Group G] where
  coeff : ℤ
  rep : ActualUnitaryGroupRepresentation G

abbrev FiniteUnitaryVirtualRepresentation (G : Type u) [Group G] :=
  List (UnitaryVirtualSummand G)

namespace FiniteUnitaryVirtualRepresentation

variable {G : Type u} [Group G]

/-- Forget only the invariant-inner-product certificate. -/
def toFiniteVirtual : FiniteUnitaryVirtualRepresentation G →
    FiniteVirtualGroupRepresentation G
  | [] => []
  | s :: source =>
      { coeff := s.coeff
        rep := s.rep.toActualGroupRepresentation } :: toFiniteVirtual source

/-- Aggregate every positive coefficient into one actual unitary
representation. -/
def positive : FiniteUnitaryVirtualRepresentation G →
    ActualUnitaryGroupRepresentation G
  | [] => .zero
  | s :: source => .product (.copies s.coeff.toNat s.rep) (positive source)

/-- Aggregate the magnitudes of every negative coefficient into one actual
unitary representation. -/
def negative : FiniteUnitaryVirtualRepresentation G →
    ActualUnitaryGroupRepresentation G
  | [] => .zero
  | s :: source => .product (.copies (-s.coeff).toNat s.rep) (negative source)

/-- The positive-minus-negative aggregate has exactly the original virtual
character. -/
theorem positive_character_sub_negative_character
    (source : FiniteUnitaryVirtualRepresentation G) (g : G) :
    (positive source).rho.character g - (negative source).rho.character g =
      FiniteVirtualGroupRepresentation.character (toFiniteVirtual source) g := by
  induction source with
  | nil =>
      change
        ActualUnitaryGroupRepresentation.zero.rho.character g -
            ActualUnitaryGroupRepresentation.zero.rho.character g = 0
      rw [ActualUnitaryGroupRepresentation.zero_character]
      ring
  | cons s source ih =>
      rw [positive, negative,
        ActualUnitaryGroupRepresentation.product_character,
        ActualUnitaryGroupRepresentation.product_character,
        ActualUnitaryGroupRepresentation.copies_character,
        ActualUnitaryGroupRepresentation.copies_character]
      have hcoeffInt := s.coeff.toNat_sub_toNat_neg
      have hcoeff := congrArg (fun z : ℤ => (z : ℂ)) hcoeffInt
      simp only [Int.cast_sub, Int.cast_natCast] at hcoeff
      have hcoeff' :
        (s.coeff.toNat : ℂ) - ((-s.coeff).toNat : ℂ) =
            (s.coeff : ℂ) := hcoeff
      simp only [toFiniteVirtual,
        FiniteVirtualGroupRepresentation.character,
        VirtualGroupSummand.character,
        ActualGroupRepresentation.character,
        ActualUnitaryGroupRepresentation.toActualGroupRepresentation]
      rw [← ih]
      calc
        _ = ((s.coeff.toNat : ℂ) - ((-s.coeff).toNat : ℂ)) *
              s.rep.rho.character g +
            ((positive source).rho.character g -
              (negative source).rho.character g) := by ring
        _ = (s.coeff : ℂ) * s.rep.rho.character g +
            ((positive source).rho.character g -
              (negative source).rho.character g) := by rw [hcoeff']

/-- Nonnegative virtual multiplicities are realized by the positive
aggregate alone, without subtracting a second field space. -/
theorem positive_character_of_nonnegative
    (source : FiniteUnitaryVirtualRepresentation G)
    (hcoeff : ∀ s ∈ source, 0 ≤ s.coeff) (g : G) :
    (positive source).rho.character g =
      FiniteVirtualGroupRepresentation.character (toFiniteVirtual source) g := by
  revert hcoeff
  induction source with
  | nil =>
      intro _
      exact ActualUnitaryGroupRepresentation.zero_character g
  | cons s source ih =>
      intro hcoeff
      have hs := hcoeff s (by simp)
      have hcast : (s.coeff.toNat : ℂ) = (s.coeff : ℂ) := by
        exact_mod_cast Int.toNat_of_nonneg hs
      change (ActualUnitaryGroupRepresentation.product
          (ActualUnitaryGroupRepresentation.copies s.coeff.toNat s.rep)
          (positive source)).rho.character g =
        (s.coeff : ℂ) * s.rep.rho.character g +
          FiniteVirtualGroupRepresentation.character (toFiniteVirtual source) g
      rw [ActualUnitaryGroupRepresentation.product_character,
        ActualUnitaryGroupRepresentation.copies_character,
        hcast, ih (fun t ht => hcoeff t (List.mem_cons_of_mem s ht))]

/-- In the common mass-index interface, the canonical positive and negative
aggregates represent the supplied finite unitary virtual character. -/
theorem ultravioletIndex_characterEquivalent
    (source : FiniteUnitaryVirtualRepresentation G) :
    FiniteVirtualGroupRepresentation.CharacterEquivalent
      (ultravioletIndex
        (rhoV₀ := (positive source).rho)
        (rhoW₀ := (negative source).rho))
      (toFiniteVirtual source) := by
  intro g
  rw [ultravioletIndex_character]
  exact positive_character_sub_negative_character source g

/-!
## Structural light-mode identification
-/

/-- A mode-by-mode realization of a light index: the unmatched source kernel
is representation-isomorphic to the positive target aggregate, while the
unmatched target complement is isomorphic to the negative aggregate. -/
structure LightIndexEquiv
    {V W : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W]
    {rhoV : Representation ℂ G V} {rhoW : Representation ℂ G W}
    (f : Representation.IntertwiningMap rhoV rhoW)
    (hW : IsUnitaryRepresentation rhoW)
    (target : FiniteUnitaryVirtualRepresentation G) where
  kernelEquiv : Representation.Equiv f.ker.toRepresentation
    (positive target).rho
  cokernelEquiv : Representation.Equiv
    (orthogonalSubrepresentation rhoW hW f.range).toRepresentation
    (negative target).rho

/-- Actual representation equivalences of the two unmatched mode spaces
imply equality of the light virtual character with the target character. -/
theorem lightIndex_characterEquivalent_of_equiv
    {V W : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W]
    {rhoV : Representation ℂ G V} {rhoW : Representation ℂ G W}
    (f : Representation.IntertwiningMap rhoV rhoW)
    (hW : IsUnitaryRepresentation rhoW)
    (target : FiniteUnitaryVirtualRepresentation G)
    (e : LightIndexEquiv f hW target) :
    FiniteVirtualGroupRepresentation.CharacterEquivalent
      (lightIndex f hW) (toFiniteVirtual target) := by
  intro g
  rw [lightIndex_character]
  change
    f.ker.toRepresentation.character g -
        (orthogonalSubrepresentation rhoW hW f.range).toRepresentation.character g =
      _
  rw [congrFun (Representation.char_iso e.kernelEquiv) g,
    congrFun (Representation.char_iso e.cokernelEquiv) g]
  exact positive_character_sub_negative_character target g

end FiniteUnitaryVirtualRepresentation

end

end UnitaryVirtualRealization
end Physics
