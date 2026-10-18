import Math.RepresentationTheory.TypedMixedExchangeQuotient
import Math.RepresentationTheory.LocalRelationHom
import Math.RepresentationTheory.CommutingActionHom
import Math.RepresentationTheory.RelationQuotientNaturality

/-! Typed mixed exchange coefficients with commuting local and residual actions. -/
namespace Math.TypedMixedLocalHom
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {P Q G H : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [Group G] [Group H]
  {V : P → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  {W : Q → Type*} [∀ s, AddCommGroup (W s)] [∀ s, Module ℂ (W s)]
  (a : ∀ s, Representation ℂ G (V s)) (b : ∀ s, Representation ℂ G (W s))
  (c : ∀ s, Representation ℂ H (V s)) (d : ∀ s, Representation ℂ H (W s))
  (ha : ∀ s g h v, a s g (c s h v) = c s h (a s g v))
  (hb : ∀ s g h w, b s g (d s h w) = d s h (b s g w))
  {n m : ℕ} (p : Fin n → P) (s : Fin m → Q)

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
include ha hb in
theorem commutes : ∀ g h u,
    TypedMixedExchangeQuotient.action a b p s g (TypedMixedExchangeQuotient.action c d p s h u) =
      TypedMixedExchangeQuotient.action c d p s h (TypedMixedExchangeQuotient.action a b p s g u) := by
  intro g h
  have he : (TypedMixedExchangeQuotient.action a b p s g).comp
      (TypedMixedExchangeQuotient.action c d p s h) =
      (TypedMixedExchangeQuotient.action c d p s h).comp
        (TypedMixedExchangeQuotient.action a b p s g) := by
    apply TypedMixedTensorHom.pure_ext
    intro v w
    simp only [TypedMixedExchangeQuotient.action, LinearMap.comp_apply,
      Representation.tprod_apply, TensorProduct.map_tmul,
      MultilinearInvariantHom.tensorRepresentation_tprod, ha, hb]
  exact LinearMap.congr_fun he

def fermion (u : P) := CommutingActionHom.action (a u) (c u) (ha u)
def boson (u : Q) := CommutingActionHom.action (b u) (d u) (hb u)

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem combined_eq : TypedMixedExchangeQuotient.action
    (fermion a c ha) (boson b d hb) p s =
    CommutingActionHom.action (TypedMixedExchangeQuotient.action a b p s)
      (TypedMixedExchangeQuotient.action c d p s) (commutes a b c d ha hb p s) := by
  ext ⟨g,h⟩ : 1
  apply TypedMixedTensorHom.pure_ext
  intro v w
  simp only [TypedMixedExchangeQuotient.action, fermion, boson,
    CommutingActionHom.action_apply, Representation.tprod_apply, TensorProduct.map_tmul,
    MultilinearInvariantHom.tensorRepresentation_tprod]

abbrev residual := LocalRelationHom.residual
  (TypedMixedExchangeQuotient.action a b p s) (TypedMixedExchangeQuotient.action c d p s)
  (commutes a b c d ha hb p s) (TypedMixedExchangeQuotient.relations p s)
  (TypedMixedExchangeQuotient.stable c d p s)

def combinedConstraintsEquiv :
    RelationQuotient.vanishing
      (TypedMixedExchangeQuotient.action (fermion a c ha) (boson b d hb) p s)
      (trivial ℂ (G × H) ℂ) (TypedMixedExchangeQuotient.relations p s) ≃ₗ[ℂ]
    RelationQuotient.vanishing
      (CommutingActionHom.action (TypedMixedExchangeQuotient.action a b p s)
        (TypedMixedExchangeQuotient.action c d p s) (commutes a b c d ha hb p s))
      ((trivial ℂ H ℂ).comp (MonoidHom.snd G H)) (TypedMixedExchangeQuotient.relations p s) :=
  RelationQuotientNaturality.congrDirect _ _ _
    (combined_eq a b c d ha hb p s) (by ext z; rfl)

def inputEquiv : MixedPatternAssembly.orderedSpace (fermion a c ha) (boson b d hb) p s ≃ₗ[ℂ]
    LocalRelationHom.Input (TypedMixedExchangeQuotient.action a b p s)
      (TypedMixedExchangeQuotient.action c d p s) (trivial ℂ H ℂ)
      (TypedMixedExchangeQuotient.relations p s) :=
  (TypedMixedExchangeQuotient.constrainedEquiv (fermion a c ha) (boson b d hb) p s).trans
    ((combinedConstraintsEquiv a b c d ha hb p s).trans
      (LocalRelationHom.combinedEquiv
        (TypedMixedExchangeQuotient.action a b p s) (TypedMixedExchangeQuotient.action c d p s)
        (trivial ℂ H ℂ) (commutes a b c d ha hb p s) (TypedMixedExchangeQuotient.relations p s)))

def equiv : MixedPatternAssembly.orderedSpace (fermion a c ha) (boson b d hb) p s ≃ₗ[ℂ]
    IntertwiningMap (residual a b c d ha hb p s) (trivial ℂ H ℂ) :=
  (inputEquiv a b c d ha hb p s).trans (LocalRelationHom.equiv
          (TypedMixedExchangeQuotient.action a b p s) (TypedMixedExchangeQuotient.action c d p s)
          (trivial ℂ H ℂ) (commutes a b c d ha hb p s) (TypedMixedExchangeQuotient.relations p s)
          (TypedMixedExchangeQuotient.stable c d p s))

def familyEquiv : MixedPatternAssembly.familySpace (fermion a c ha) (boson b d hb) p s ≃ₗ[ℂ]
    IntertwiningMap (residual a b c d ha hb p s) (trivial ℂ H ℂ) :=
  (MixedPatternAssembly.equiv (fermion a c ha) (boson b d hb) p s).trans
    (equiv a b c d ha hb p s)


end
end Math.TypedMixedLocalHom
