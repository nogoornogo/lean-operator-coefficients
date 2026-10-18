/-!
# Flipped-branch character obstruction

This file formalizes the first algebraic milestone from `CODEX_TASK.md`.

We work in the Laurent character ring of the flipped subtorus after imposing

* `z1 * z2 * z3 * z4 * z5 * z6 = 1`, the `SU(6)` torus relation, and
* `z4 * z5 = 1`, the flipped Standard Model torus relation.

Thus the coordinate ring is modeled as the Laurent polynomial ring on
`z1,z2,z3,z4`, with

* `z5 = z4^-1`,
* `z6 = (z1*z2*z3)^-1`.

The transposition `(3 6)` acts by fixing `z1,z2,z4` and sending
`z3` to `z6`.

The explicit character algebra is combined with a small bridge theorem:
ambient Weyl-invariant characters restrict to characters invariant under the
induced action on any preserved subtorus. What is still not formalized here is
the Lie-theoretic theorem that finite-dimensional `SU(6)` characters are
ambient Weyl-invariant.
-/

namespace GUT
namespace Flipped

structure Exp where
  z1 : Int
  z2 : Int
  z3 : Int
  z4 : Int
deriving Repr, DecidableEq

structure Term where
  exp : Exp
  coeff : Int
deriving Repr, DecidableEq

structure Poly where
  terms : List Term
deriving Repr, DecidableEq

namespace Exp

def add (a b : Exp) : Exp :=
  { z1 := a.z1 + b.z1
    z2 := a.z2 + b.z2
    z3 := a.z3 + b.z3
    z4 := a.z4 + b.z4 }

def neg (a : Exp) : Exp :=
  { z1 := -a.z1
    z2 := -a.z2
    z3 := -a.z3
    z4 := -a.z4 }

def cmpInt (a b : Int) : Ordering :=
  if a < b then
    .lt
  else if a = b then
    .eq
  else
    .gt

def cmp (a b : Exp) : Ordering :=
  match cmpInt a.z1 b.z1 with
  | .eq =>
      match cmpInt a.z2 b.z2 with
      | .eq =>
          match cmpInt a.z3 b.z3 with
          | .eq => cmpInt a.z4 b.z4
          | ord => ord
      | ord => ord
  | ord => ord

end Exp

namespace Poly

def zero : Poly := { terms := [] }

def insertTerm (e : Exp) (c : Int) : List Term -> List Term
  | [] =>
      if c = 0 then
        []
      else
        [{ exp := e, coeff := c }]
  | t :: ts =>
      match Exp.cmp e t.exp with
      | .lt =>
          if c = 0 then
            t :: ts
          else
            { exp := e, coeff := c } :: t :: ts
      | .eq =>
          let c' := c + t.coeff
          if c' = 0 then
            ts
          else
            { exp := e, coeff := c' } :: ts
      | .gt =>
          t :: insertTerm e c ts

def ofTerm (e : Exp) (c : Int) : Poly :=
  { terms := insertTerm e c [] }

def add (p q : Poly) : Poly :=
  { terms := q.terms.foldl (fun acc t => insertTerm t.exp t.coeff acc) p.terms }

def neg (p : Poly) : Poly :=
  { terms := p.terms.map (fun t => { exp := t.exp, coeff := -t.coeff }) }

def sub (p q : Poly) : Poly :=
  add p (neg q)

def mul (p q : Poly) : Poly :=
  { terms :=
      p.terms.foldl
        (fun acc t =>
          q.terms.foldl
            (fun acc u => insertTerm (Exp.add t.exp u.exp) (t.coeff * u.coeff) acc)
            acc)
        [] }

def mapExp (f : Exp -> Exp) (p : Poly) : Poly :=
  { terms := p.terms.foldl (fun acc t => insertTerm (f t.exp) t.coeff acc) [] }

def zscale (n : Int) (p : Poly) : Poly :=
  { terms := p.terms.map (fun t => { exp := t.exp, coeff := n * t.coeff }) }

instance : Zero Poly := ⟨zero⟩
instance : Neg Poly := ⟨neg⟩
instance : Add Poly := ⟨add⟩
instance : Sub Poly := ⟨sub⟩
instance : Mul Poly := ⟨mul⟩

end Poly

def mon (z1 z2 z3 z4 coeff : Int) : Poly :=
  Poly.ofTerm { z1 := z1, z2 := z2, z3 := z3, z4 := z4 } coeff

def one : Poly := mon 0 0 0 0 1

def z1 : Poly := mon 1 0 0 0 1
def z2 : Poly := mon 0 1 0 0 1
def z3 : Poly := mon 0 0 1 0 1
def z4 : Poly := mon 0 0 0 1 1
def z5 : Poly := mon 0 0 0 (-1) 1
def z6 : Poly := mon (-1) (-1) (-1) 0 1

def invZ1 : Poly := mon (-1) 0 0 0 1
def invZ2 : Poly := mon 0 (-1) 0 0 1
def invZ3 : Poly := mon 0 0 (-1) 0 1
def invZ4 : Poly := z5
def invZ5 : Poly := z4
def invZ6 : Poly := mon 1 1 1 0 1

def colorTriplet : Poly :=
  z1 + z2 + z3

def colorAntiTriplet : Poly :=
  invZ1 + invZ2 + invZ3

def weakDoublet : Poly :=
  z4 + z5

theorem weak_relation_z4_z5 :
    z4 * z5 = one := by
  decide

theorem su6_torus_relation :
    z1 * z2 * z3 * z4 * z5 * z6 = one := by
  decide

/- The chiral character of the virtual fundamental, `χ_6 - χ_{\bar 6}`. -/
def D6 : Poly :=
  colorTriplet + z6 - colorAntiTriplet - invZ6

/- The second factor `W - t^3 - t^-3`, rewritten as `W - z6^-1 - z6`. -/
def A : Poly :=
  weakDoublet - invZ6 - z6

/- The one-family flipped Standard Model chiral character, term by term. -/
def flippedSMCharacterExplicit : Poly :=
  colorTriplet * weakDoublet
    - colorAntiTriplet * weakDoublet
    + colorAntiTriplet * (z6 + invZ6)
    - colorTriplet * (z6 + invZ6)
    + weakDoublet * (z6 - invZ6)
    + (invZ6 * invZ6 - z6 * z6)

/- The same character in the proposed factored form. -/
def flippedSMCharacter : Poly :=
  D6 * A

def swap36Exp (e : Exp) : Exp :=
  { z1 := e.z1 - e.z3
    z2 := e.z2 - e.z3
    z3 := -e.z3
    z4 := e.z4 }

def swap36 (p : Poly) : Poly :=
  Poly.mapExp swap36Exp p

/-!
## Ambient SU(6) torus lattice and the restriction bridge

The ambient `SU(6)` torus character lattice is represented by five independent
coordinates. The sixth coordinate is eliminated using
`x6 = (x1*x2*x3*x4*x5)^-1`.

The flipped subtorus restriction sends

* `x1,x2,x3` to the color coordinates,
* `x4` to the weak coordinate `z4`,
* `x5` to `z5 = z4^-1`.

The theorem `AmbientExp.restrict_swap36` is the key lattice bridge: the ambient
Weyl transposition `(3 6)`, followed by restriction, is the same map as
restriction followed by the subtorus action `swap36Exp`.
-/

structure AmbientExp where
  z1 : Int
  z2 : Int
  z3 : Int
  z4 : Int
  z5 : Int
deriving Repr, DecidableEq

namespace AmbientExp

def swap36 (e : AmbientExp) : AmbientExp :=
  { z1 := e.z1 - e.z3
    z2 := e.z2 - e.z3
    z3 := -e.z3
    z4 := e.z4 - e.z3
    z5 := e.z5 - e.z3 }

def restrictFlipped (e : AmbientExp) : Exp :=
  { z1 := e.z1
    z2 := e.z2
    z3 := e.z3
    z4 := e.z4 - e.z5 }

theorem restrict_swap36 (e : AmbientExp) :
    restrictFlipped (swap36 e) = swap36Exp (restrictFlipped e) := by
  cases e
  simp [restrictFlipped, swap36, swap36Exp]
  omega

theorem swap36_involutive (e : AmbientExp) :
    swap36 (swap36 e) = e := by
  cases e
  simp [swap36]

end AmbientExp

/-!
## Abstract character-restriction bridge

This section records the representation-theoretic logic without assuming the
flipped obstruction itself. If an ambient character is fixed by the ambient
Weyl transposition `(3 6)`, and the chosen subtorus is preserved by that
transposition, then the restricted character is fixed by the induced action on
the subtorus.

For actual finite-dimensional `SU(6)` representations, this standard input is
supplied in `GUT.ActualRestriction`: their characters are invariant under
Weyl representatives because characters are conjugacy-invariant.
-/

structure AmbientPoint (α : Type u) where
  z1 : α
  z2 : α
  z3 : α
  z4 : α
  z5 : α
  z6 : α
deriving Repr

namespace AmbientPoint

@[ext]
theorem ext
    {p q : AmbientPoint α}
    (h1 : p.z1 = q.z1)
    (h2 : p.z2 = q.z2)
    (h3 : p.z3 = q.z3)
    (h4 : p.z4 = q.z4)
    (h5 : p.z5 = q.z5)
    (h6 : p.z6 = q.z6) :
    p = q := by
  cases p
  cases q
  simp_all

def swap36 (p : AmbientPoint α) : AmbientPoint α :=
  { z1 := p.z1
    z2 := p.z2
    z3 := p.z6
    z4 := p.z4
    z5 := p.z5
    z6 := p.z3 }

theorem swap36_involutive (p : AmbientPoint α) :
    swap36 (swap36 p) = p := by
  cases p
  rfl

end AmbientPoint

structure WeylInvariantCharacter (α : Type u) (β : Type v) where
  toFun : AmbientPoint α -> β
  swap36_fixed : ∀ p : AmbientPoint α, toFun (AmbientPoint.swap36 p) = toFun p

namespace WeylInvariantCharacter

def restrictToSubtorus
    {α : Type u} {β : Type v}
    {Subtorus : AmbientPoint α -> Prop}
    (χ : WeylInvariantCharacter α β)
    (p : { q : AmbientPoint α // Subtorus q }) : β :=
  χ.toFun p.val

def inducedSwap36
    {α : Type u}
    {Subtorus : AmbientPoint α -> Prop}
    (hSubtorus : ∀ p : AmbientPoint α, Subtorus p -> Subtorus (AmbientPoint.swap36 p))
    (p : { q : AmbientPoint α // Subtorus q }) :
    { q : AmbientPoint α // Subtorus q } :=
  ⟨AmbientPoint.swap36 p.val, hSubtorus p.val p.property⟩

theorem restricted_swap36_fixed
    {α : Type u} {β : Type v}
    {Subtorus : AmbientPoint α -> Prop}
    (hSubtorus : ∀ p : AmbientPoint α, Subtorus p -> Subtorus (AmbientPoint.swap36 p))
    (χ : WeylInvariantCharacter α β)
    (p : { q : AmbientPoint α // Subtorus q }) :
    restrictToSubtorus χ (inducedSwap36 hSubtorus p)
      = restrictToSubtorus χ p := by
  exact χ.swap36_fixed p.val

end WeylInvariantCharacter

/-!
## Conjugacy-invariance route to Weyl-invariance

This is the group-theoretic reason finite-dimensional representation
characters should satisfy the ambient Weyl-invariance hypothesis above.  We do
not formalize matrices or traces here; instead we isolate the exact logical
step needed from standard representation theory.
-/

structure WeylActionByConjugation (GroupPoint : Type u) (TorusPoint : Type v) where
  incl : TorusPoint -> GroupPoint
  action : TorusPoint -> TorusPoint
  conjugateByRepresentative : GroupPoint -> GroupPoint
  action_eq_conjugate :
    ∀ t : TorusPoint, incl (action t) = conjugateByRepresentative (incl t)

structure FixedByConjugation
    (GroupPoint : Type u) (Values : Type v)
    (conjugateByRepresentative : GroupPoint -> GroupPoint) where
  toFun : GroupPoint -> Values
  conjugation_fixed :
    ∀ g : GroupPoint, toFun (conjugateByRepresentative g) = toFun g

namespace FixedByConjugation

def restrictAlong
    {GroupPoint : Type u} {TorusPoint : Type v} {Values : Type w}
    (data : WeylActionByConjugation GroupPoint TorusPoint)
    (χ : FixedByConjugation GroupPoint Values data.conjugateByRepresentative)
    (t : TorusPoint) : Values :=
  χ.toFun (data.incl t)

theorem restricted_fixed_by_weyl_action
    {GroupPoint : Type u} {TorusPoint : Type v} {Values : Type w}
    (data : WeylActionByConjugation GroupPoint TorusPoint)
    (χ : FixedByConjugation GroupPoint Values data.conjugateByRepresentative)
    (t : TorusPoint) :
    restrictAlong data χ (data.action t) = restrictAlong data χ t := by
  rw [restrictAlong, data.action_eq_conjugate]
  exact χ.conjugation_fixed (data.incl t)

end FixedByConjugation

/-!
## Trace characters of finite-dimensional representations

A finite-dimensional representation gives a matrix algebra of endomorphisms and
a trace.  Instead of developing matrices from scratch in this no-dependency
project, the exact algebraic properties of that situation are packaged as
`TraceAlgebra`: associative multiplication, a unit, and cyclicity of trace.

This is enough to prove that the trace character of any representation is
invariant under conjugation.
-/

structure GroupOps (G : Type u) where
  one : G
  mul : G -> G -> G
  inv : G -> G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G, mul one a = a
  mul_one : ∀ a : G, mul a one = a
  inv_mul_cancel : ∀ a : G, mul (inv a) a = one
  mul_inv_cancel : ∀ a : G, mul a (inv a) = one

namespace GroupOps

def conj (grp : GroupOps G) (n g : G) : G :=
  grp.mul (grp.mul n g) (grp.inv n)

end GroupOps

structure TraceAlgebra (End : Type u) (Values : Type v) where
  one : End
  mul : End -> End -> End
  trace : End -> Values
  mul_assoc : ∀ a b c : End, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : End, mul one a = a
  mul_one : ∀ a : End, mul a one = a
  trace_mul_comm : ∀ a b : End, trace (mul a b) = trace (mul b a)

structure TraceRepresentation (G : Type u) (End : Type v) (Values : Type w) where
  group : GroupOps G
  alg : TraceAlgebra End Values
  rho : G -> End
  map_mul : ∀ a b : G, rho (group.mul a b) = alg.mul (rho a) (rho b)
  map_one : rho group.one = alg.one
  map_inv_mul : ∀ a : G, alg.mul (rho (group.inv a)) (rho a) = alg.one
  map_mul_inv : ∀ a : G, alg.mul (rho a) (rho (group.inv a)) = alg.one

namespace TraceRepresentation

def character (ρ : TraceRepresentation G End Values) (g : G) : Values :=
  ρ.alg.trace (ρ.rho g)

theorem character_conjugation_fixed
    (ρ : TraceRepresentation G End Values) (n g : G) :
    ρ.character (ρ.group.conj n g) = ρ.character g := by
  calc
    ρ.character (ρ.group.conj n g)
        = ρ.alg.trace
            (ρ.alg.mul (ρ.alg.mul (ρ.rho n) (ρ.rho g))
              (ρ.rho (ρ.group.inv n))) := by
          simp [character, GroupOps.conj, ρ.map_mul]
    _ = ρ.alg.trace
            (ρ.alg.mul (ρ.rho (ρ.group.inv n))
              (ρ.alg.mul (ρ.rho n) (ρ.rho g))) := by
          exact ρ.alg.trace_mul_comm
            (ρ.alg.mul (ρ.rho n) (ρ.rho g))
            (ρ.rho (ρ.group.inv n))
    _ = ρ.alg.trace
            (ρ.alg.mul (ρ.alg.mul (ρ.rho (ρ.group.inv n)) (ρ.rho n))
              (ρ.rho g)) := by
          rw [ρ.alg.mul_assoc]
    _ = ρ.alg.trace (ρ.alg.mul ρ.alg.one (ρ.rho g)) := by
          rw [ρ.map_inv_mul]
    _ = ρ.character g := by
          rw [ρ.alg.one_mul]
          rfl

def fixedByConjugationMap
    (ρ : TraceRepresentation G End Values)
    (n : G)
    (conjugateByRepresentative : G -> G)
    (hconj : ∀ g : G, conjugateByRepresentative g = ρ.group.conj n g) :
    FixedByConjugation G Values conjugateByRepresentative where
  toFun := ρ.character
  conjugation_fixed := by
    intro g
    rw [hconj g]
    exact ρ.character_conjugation_fixed n g

end TraceRepresentation

/-!
## The `(3 6)` Weyl representative as a coordinate permutation

The actual matrix representative is constructed in `GUT.WeylMatrix`, and
connected back to this point-level model in `GUT.ConcreteBridge`.  The data
below is the torus-level effect that such a representative must have:
conjugating a diagonal torus point by the representative swaps the third and
sixth coordinates.
-/

def swap36WeylActionData (α : Type u) :
    WeylActionByConjugation (AmbientPoint α) (AmbientPoint α) where
  incl := fun t => t
  action := AmbientPoint.swap36
  conjugateByRepresentative := AmbientPoint.swap36
  action_eq_conjugate := by
    intro t
    rfl

theorem swap36WeylActionData_z3 (p : AmbientPoint α) :
    ((swap36WeylActionData α).action p).z3 = p.z6 := by
  rfl

theorem swap36WeylActionData_z6 (p : AmbientPoint α) :
    ((swap36WeylActionData α).action p).z6 = p.z3 := by
  rfl

theorem swap36WeylActionData_z4 (p : AmbientPoint α) :
    ((swap36WeylActionData α).action p).z4 = p.z4 := by
  rfl

/-!
## Finite Laurent character model

The character of a finite-dimensional torus representation is a finite
integer-linear combination of weights.  `RawCharacter` records exactly that:
a finite list of weighted monomials.  The theorem `restrict_ambientSwap36`
checks that restricting ambient Laurent monomials to the flipped lattice
commutes with the `(3 6)` Weyl action.
-/

structure WeightedMonomial (Exponent : Type u) where
  exp : Exponent
  coeff : Int
deriving Repr, DecidableEq

abbrev RawCharacter (Exponent : Type u) := List (WeightedMonomial Exponent)

namespace RawCharacter

def mapExp {E : Type u} {F : Type v}
    (f : E -> F) (χ : RawCharacter E) : RawCharacter F :=
  χ.map (fun m => { exp := f m.exp, coeff := m.coeff })

def ambientSwap36 (χ : RawCharacter AmbientExp) : RawCharacter AmbientExp :=
  mapExp AmbientExp.swap36 χ

def restrictFlipped (χ : RawCharacter AmbientExp) : RawCharacter Exp :=
  mapExp AmbientExp.restrictFlipped χ

def subtorusSwap36 (χ : RawCharacter Exp) : RawCharacter Exp :=
  mapExp swap36Exp χ

theorem mapExp_comp
    {E : Type u} {F : Type v} {H : Type w}
    (f : E -> F) (g : F -> H) (χ : RawCharacter E) :
    mapExp g (mapExp f χ) = mapExp (fun e => g (f e)) χ := by
  induction χ with
  | nil => rfl
  | cons m ms ih =>
      cases m
      simp [mapExp]

theorem restrict_ambientSwap36 (χ : RawCharacter AmbientExp) :
    restrictFlipped (ambientSwap36 χ)
      = subtorusSwap36 (restrictFlipped χ) := by
  induction χ with
  | nil => rfl
  | cons m ms ih =>
      cases m
      simp [restrictFlipped, ambientSwap36, subtorusSwap36, mapExp,
        AmbientExp.restrict_swap36]

theorem restrict_fixed_of_ambient_fixed
    (χ : RawCharacter AmbientExp)
    (hχ : ambientSwap36 χ = χ) :
    subtorusSwap36 (restrictFlipped χ) = restrictFlipped χ := by
  calc
    subtorusSwap36 (restrictFlipped χ)
        = restrictFlipped (ambientSwap36 χ) := by
          exact (restrict_ambientSwap36 χ).symm
    _ = restrictFlipped χ := by
          rw [hχ]

def toPoly (χ : RawCharacter Exp) : Poly :=
  { terms :=
      χ.foldl
        (fun acc m => Poly.insertTerm m.exp m.coeff acc)
        [] }

def restrictFlippedToPoly (χ : RawCharacter AmbientExp) : Poly :=
  toPoly (restrictFlipped χ)

theorem finite_laurent_model_exists (χ : RawCharacter AmbientExp) :
    ∃ p : Poly, p = restrictFlippedToPoly χ := by
  exact ⟨restrictFlippedToPoly χ, rfl⟩

end RawCharacter

theorem swap36_z1 : swap36 z1 = z1 := by
  decide

theorem swap36_z2 : swap36 z2 = z2 := by
  decide

theorem swap36_z3 : swap36 z3 = z6 := by
  decide

theorem swap36_z4 : swap36 z4 = z4 := by
  decide

theorem swap36_z5 : swap36 z5 = z5 := by
  decide

theorem swap36_z6 : swap36 z6 = z3 := by
  decide

theorem swap36_preserves_weak_relation :
    swap36 z4 * swap36 z5 = one := by
  decide

theorem swap36_preserves_su6_torus_relation :
    swap36 z1 * swap36 z2 * swap36 z3 * swap36 z4 * swap36 z5 * swap36 z6 = one := by
  decide

theorem flippedSM_factorization :
    flippedSMCharacterExplicit = flippedSMCharacter := by
  decide

theorem swap36_D6 :
    swap36 D6 = D6 := by
  decide

theorem swap36_A_ne :
    swap36 A ≠ A := by
  decide

theorem swap36_A_formula :
    swap36 A = weakDoublet - invZ3 - z3 := by
  decide

theorem swap36_flippedSM_ne :
    swap36 flippedSMCharacter ≠ flippedSMCharacter := by
  decide

theorem swap36_flippedSMExplicit_ne :
    swap36 flippedSMCharacterExplicit ≠ flippedSMCharacterExplicit := by
  decide

/-!
The representation-theoretic bridge is intentionally not hidden.

Within this raw polynomial interface, a no-uplift theorem follows from the
displayed fixedness hypothesis.  `GUT.NormalizedLaurent` later proves a
stronger function-level theorem for arbitrary finite virtual `SU(6)`
restricted characters, without requiring a Laurent polynomial for each source
representation.
-/
theorem no_flipped_sm_uplift_conditional
    {SU6VirtualCharacter : Type}
    (restrictFlipped : SU6VirtualCharacter -> Poly)
    (relativeWeylInvariant :
      ∀ χ : SU6VirtualCharacter, swap36 (restrictFlipped χ) = restrictFlipped χ) :
    ¬ ∃ χ : SU6VirtualCharacter, restrictFlipped χ = flippedSMCharacter := by
  intro h
  rcases h with ⟨χ, hχ⟩
  have hInvariant := relativeWeylInvariant χ
  rw [hχ] at hInvariant
  exact swap36_flippedSM_ne hInvariant

end Flipped
end GUT
