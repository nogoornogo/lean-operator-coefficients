import Math.RepresentationTheory.TypedMixedLocalHom

/-! Evaluation formulas for the actual-field to local/residual presentation. -/
namespace Math.TypedMixedLocalHom
set_option autoImplicit false
noncomputable section
open Representation
variable {P Q G H : Type*} [DecidableEq P] [DecidableEq Q] [Group G] [Group H]
  {V : P → Type*} [∀ u, AddCommGroup (V u)] [∀ u, Module ℂ (V u)]
  {W : Q → Type*} [∀ u, AddCommGroup (W u)] [∀ u, Module ℂ (W u)]
  (a : ∀ u, Representation ℂ G (V u)) (b : ∀ u, Representation ℂ G (W u))
  (c : ∀ u, Representation ℂ H (V u)) (d : ∀ u, Representation ℂ H (W u))
  (ha : ∀ u g h v, a u g (c u h v) = c u h (a u g v))
  (hb : ∀ u g h v, b u g (d u h v) = d u h (b u g v))
  {n m : ℕ} (p : Fin n → P) (s : Fin m → Q)

omit [DecidableEq P] [DecidableEq Q] in
theorem combinedConstraintsEquiv_apply
    (q : RelationQuotient.vanishing
      (TypedMixedExchangeQuotient.action (fermion a c ha) (boson b d hb) p s)
      (trivial ℂ (G × H) ℂ) (TypedMixedExchangeQuotient.relations p s))
    (u : TypedMixedExchangeQuotient.Domain (V := V) (W := W) p s) :
    (combinedConstraintsEquiv a b c d ha hb p s q).val u = q.val u := by
  rfl

theorem inputEquiv_apply
    (q : MixedPatternAssembly.orderedSpace (fermion a c ha) (boson b d hb) p s)
    (u : TypedMixedExchangeQuotient.Domain (V := V) (W := W) p s) :
    (inputEquiv a b c d ha hb p s q).val.val u = TypedMixedTensorHom.orderedEquiv.symm q.val u := by
  rfl
end
end Math.TypedMixedLocalHom
