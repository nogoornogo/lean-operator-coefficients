import Math.RepresentationTheory.LocalCoinvariantHom
import Math.RepresentationTheory.SignedRelationQuotient

/-! Exchange constraints can be imposed after local coinvariant descent,
with an explicit inverse residual-Hom classification. -/
namespace Math.LocalExchangeHom
set_option autoImplicit false
noncomputable section
open Representation
variable {k G H U W J : Type*} [Field k] [Group G] [Group H]
  [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
  (a : Representation k G U) (b : Representation k H U) (t : Representation k H W)
  (commutes : ∀ g h u, a g (b h u) = b h (a g u))
  (s : J → IntertwiningMap b b) (weight : J → k)
  (compatible : ∀ j g u, s j (a g u) = a g (s j u))

def pullback (j : J) : LocalCoinvariantHom.invariantHom a b t →ₗ[k]
    LocalCoinvariantHom.invariantHom a b t where
  toFun f := ⟨f.val.comp (s j), by
    intro g u
    change f.val (s j (a g u)) = f.val (s j u)
    rw [compatible, f.property]⟩
  map_add' f q := by apply Subtype.ext; ext u; rfl
  map_smul' z f := by apply Subtype.ext; ext u; rfl

def exchange (j : J) := LocalCoinvariantHom.descendExchange a b commutes (s j) (compatible j)

theorem transport (j : J) (f : LocalCoinvariantHom.invariantHom a b t) :
    LocalCoinvariantHom.equiv a b t commutes (pullback a b t s compatible j f) =
      SignedRelationQuotient.action (LocalCoinvariantHom.quotient a b commutes) t
        (exchange a b commutes s compatible) j (LocalCoinvariantHom.equiv a b t commutes f) := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  obtain ⟨v,rfl⟩ := (LocalCoinvariantHom.relations a).mkQ_surjective u
  rfl

abbrev Input := StatisticalCompleteness.sector (pullback a b t s compatible) weight
abbrev residual := SignedRelationQuotient.quotientRepresentation
  (LocalCoinvariantHom.quotient a b commutes) (exchange a b commutes s compatible) weight

def equiv : Input a b t s weight compatible ≃ₗ[k]
    IntertwiningMap (residual a b commutes s weight compatible) t :=
  (StatisticalCompleteness.equiv (LocalCoinvariantHom.equiv a b t commutes)
    _ _ weight (transport a b t commutes s compatible)).trans
    (SignedRelationQuotient.equiv _ t (exchange a b commutes s compatible) weight)

@[simp] theorem equiv_mk (f : Input a b t s weight compatible) (u : U) :
    equiv a b t commutes s weight compatible f
      ((SignedRelationQuotient.relations (LocalCoinvariantHom.quotient a b commutes)
        (exchange a b commutes s compatible) weight).mkQ
          ((LocalCoinvariantHom.relations a).mkQ u)) = f.val.val u := rfl

end
end Math.LocalExchangeHom
