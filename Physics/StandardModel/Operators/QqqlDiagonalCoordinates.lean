import Math.RepresentationTheory.TripleFlavorWeights
import Math.RepresentationTheory.CyclicWeightCoordinates
import Physics.StandardModel.Operators.QqqlFiniteFlavor

open Math

/-! Cyclic weights on the independent symmetric, alternating and mixed qqql
flavor coordinates. No ordered triple is counted as automatically independent. -/
namespace GUT.QqqlDiagonalCoordinates
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
variable {n m : ℕ}

def scale (w : Fin n → ℂ) (v : Fin m → ℂ) (d : QqqlFiniteFlavor.Coordinates n m) :
    QqqlFiniteFlavor.Coordinates n m :=
  fun t p => v t * TripleFlavorWeights.weight w p * d t p

theorem basisValue_scale (w : Fin n → ℂ) (v : Fin m → ℂ)
    (d : QqqlFiniteFlavor.Coordinates n m) (r : Fin 4) (i j k : Fin n) (t : Fin m) :
    QqqlFiniteFlavor.basisValue (scale w v d) r i j k t =
      (w i * w j * w k * v t) * QqqlFiniteFlavor.basisValue d r i j k t := by
  fin_cases r
  · change TripleSymmetricCoordinates.assemble
      (fun p => v t * TripleFlavorWeights.symmetricWeight w p * d t (.inl p)) i j k = _
    exact TripleFlavorWeights.symmetric_assemble (v t) w (fun p => d t (.inl p)) i j k
  · change TripleAlternatingCoordinates.assemble
      (fun p => v t * TripleFlavorWeights.alternatingWeight w p * d t (.inr (.inl p))) i j k = _
    exact TripleFlavorWeights.alternating_assemble (v t) w
      (fun p => d t (.inr (.inl p))) i j k
  · change TripleMixedCoordinates.assemble
      (fun p => v t * TripleFlavorWeights.mixedWeight w p * d t (.inr (.inr p))) j i k = _
    rw [TripleFlavorWeights.mixed_assemble]
    congr 1
    ring

  · change TripleMixedCoordinates.assemble
      (fun p => v t * TripleFlavorWeights.mixedWeight w p * d t (.inr (.inr p))) i j k = _
    exact TripleFlavorWeights.mixed_assemble (v t) w
      (fun p => d t (.inr (.inr p))) i j k

theorem basisValue_injective {d e : QqqlFiniteFlavor.Coordinates n m}
    (h : ∀ r i j k t, QqqlFiniteFlavor.basisValue d r i j k t =
      QqqlFiniteFlavor.basisValue e r i j k t) : d = e := by
  funext t
  apply (TripleFlavorCoordinates.equiv n).symm.injective
  apply Prod.ext
  · apply Subtype.ext
    funext i j k
    exact h 0 i j k t
  · apply Prod.ext
    · apply Subtype.ext
      funext i j k
      exact h 1 i j k t
    · apply Subtype.ext
      funext i j k
      exact h 3 i j k t

variable {N : ℕ} [NeZero N]

def charge (q : Fin n → ZMod N) (l : Fin m → ZMod N)
    (p : Fin m × TripleFlavorCoordinates.Index n) : ZMod N :=
  TripleFlavorWeights.charge q p.2 + l p.1

theorem scale_character (q : Fin n → ZMod N) (l : Fin m → ZMod N)
    (g : CyclicCharge.Group N) (d : QqqlFiniteFlavor.Coordinates n m)
    (t : Fin m) (p : TripleFlavorCoordinates.Index n) :
    scale (fun i => ZMod.stdAddChar (q i * Multiplicative.toAdd g))
      (fun t => ZMod.stdAddChar (l t * Multiplicative.toAdd g)) d t p =
      ZMod.stdAddChar (charge q l (t,p) * Multiplicative.toAdd g) * d t p := by
  rcases p with p | (p | (p | ⟨p,r⟩))
  all_goals
    simp only [scale, TripleFlavorWeights.weight, TripleFlavorWeights.symmetricWeight,
      TripleFlavorWeights.alternatingWeight, TripleFlavorWeights.mixedWeight,
      charge, TripleFlavorWeights.charge, TripleFlavorWeights.triple, add_mul,
      AddChar.map_add_eq_mul]
    ring

open Representation CyclicWeightCoordinates
variable {Q L : Type*} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup L] [Module ℂ L]
  (a : Representation ℂ (CyclicCharge.Group N) Q)
  (b : Representation ℂ (CyclicCharge.Group N) L)
  (qb : Module.Basis (Fin n) ℂ Q) (lb : Module.Basis (Fin m) ℂ L)
  (q : Fin n → ZMod N) (l : Fin m → ZMod N)

theorem raw_scale (hq : IsWeightBasis a qb q) (hl : IsWeightBasis b lb l)
    (g : CyclicCharge.Group N) (d : QqqlFiniteFlavor.Coordinates n m) (r : Fin 4) :
    QqqlFiniteFlavor.raw qb lb
      (scale (fun i => ZMod.stdAddChar (q i * Multiplicative.toAdd g))
        (fun t => ZMod.stdAddChar (l t * Multiplicative.toAdd g)) d) r =
    (QqqlFiniteFlavor.raw qb lb d r).comp (((a.tprod a).tprod (a.tprod b)) g) := by
  apply (QqqlFiniteFlavor.tensorBasis qb lb).ext
  rintro ⟨⟨i,j⟩,⟨k,t⟩⟩
  simp only [QqqlFiniteFlavor.tensorBasis, Module.Basis.tensorProduct_apply,
    LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul,
    hq g, hl g, TensorProduct.smul_tmul_smul, map_smul, smul_eq_mul,
    QqqlFiniteFlavor.raw_basis, basisValue_scale]
  ring

theorem residual_iff_scale (hq : IsWeightBasis a qb q) (hl : IsWeightBasis b lb l)
    (d : QqqlFiniteFlavor.Coordinates n m) :
    QqqlFiniteFlavor.ResidualCondition a b qb lb d ↔
      ∀ g, scale (fun i => ZMod.stdAddChar (q i * Multiplicative.toAdd g))
        (fun t => ZMod.stdAddChar (l t * Multiplicative.toAdd g)) d = d := by
  constructor
  · intro hd g
    apply basisValue_injective
    intro r i j k t
    have hr := (raw_scale a b qb lb q l hq hl g d r).trans (hd r g)
    have he := DFunLike.congr_fun hr ((qb i ⊗ₜ[ℂ] qb j) ⊗ₜ[ℂ] (qb k ⊗ₜ[ℂ] lb t))
    simpa only [LinearMap.comp_apply, trivial_apply, QqqlFiniteFlavor.raw_basis] using he
  · intro hd r g
    rw [← raw_scale a b qb lb q l hq hl g d r, hd g]
    ext x
    rfl

theorem residual_iff_supported (hq : IsWeightBasis a qb q) (hl : IsWeightBasis b lb l)
    (d : QqqlFiniteFlavor.Coordinates n m) :
    QqqlFiniteFlavor.ResidualCondition a b qb lb d ↔
      QqqlFiniteFlavor.flatten d ∈ supported (charge q l) := by
  rw [residual_iff_scale a b qb lb q l hq hl d]
  constructor
  · intro hd p hp
    by_contra hn
    apply hp
    apply (CyclicCharge.neutral_iff _).mp
    intro g
    have he := congrFun (congrFun (hd g) p.1) p.2
    rw [scale_character] at he
    exact mul_right_cancel₀ hn (he.trans (one_mul _).symm)
  · intro hd g
    funext t p
    rw [scale_character]
    by_cases h : charge q l (t,p) = 0
    · simp [h]
    · have hz := hd (t,p) h
      change d t p = 0 at hz
      simp [hz]

def spaceEquiv (hq : IsWeightBasis a qb q) (hl : IsWeightBasis b lb l) :
    QqqlFiniteFlavor.space a b qb lb ≃ₗ[ℂ] supported (charge q l) where
  toFun d := ⟨QqqlFiniteFlavor.flatten d.val,
    (residual_iff_supported a b qb lb q l hq hl d.val).mp d.property⟩
  invFun d := ⟨QqqlFiniteFlavor.flatten.symm d.val,
    (residual_iff_supported a b qb lb q l hq hl _).mpr d.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def equiv (hq : IsWeightBasis a qb q) (hl : IsWeightBasis b lb l) :
    QqqlExteriorCompleteness.Sector a b ≃ₗ[ℂ]
      ({p // charge q l p = 0} → ℂ) :=
  (QqqlFiniteFlavor.exteriorEquiv a b qb lb).trans
    ((spaceEquiv a b qb lb q l hq hl).trans (supportedEquiv (charge q l)))

theorem finrank (hq : IsWeightBasis a qb q) (hl : IsWeightBasis b lb l) :
    Module.finrank ℂ (QqqlExteriorCompleteness.Sector a b) =
      Fintype.card {p // charge q l p = 0} := by
  rw [(equiv a b qb lb q l hq hl).finrank_eq]
  simp

theorem allowed_iff (hq : IsWeightBasis a qb q) (hl : IsWeightBasis b lb l) :
    SelectionCriteria.Allowed (QqqlExteriorCompleteness.Sector a b) ↔
      ∃ p, charge q l p = 0 := by
  rw [SelectionCriteria.allowed_equiv (equiv a b qb lb q l hq hl)]
  constructor
  · rintro ⟨d,hd⟩
    by_contra hn
    apply hd
    funext p
    exact False.elim (hn ⟨p.val,p.property⟩)
  · rintro ⟨p,hp⟩
    exact ⟨fun _ => 1, by intro h; have he := congrFun h ⟨p,hp⟩; simp at he⟩

section FiniteIndices
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def finiteBasis (I : Type*) [Fintype I] [DecidableEq I] :
    Module.Basis (Fin (Fintype.card I)) ℂ (I → ℂ) :=
  (Pi.basisFun ℂ I).reindex (Fintype.equivFin I)

theorem finite_weights (q : I → ZMod N) :
    IsWeightBasis (diagonal q) (finiteBasis I) (q ∘ (Fintype.equivFin I).symm) := by
  intro g i
  simp only [finiteBasis, Module.Basis.reindex_apply, Function.comp_apply]
  exact diagonal_basis q g _

def diagonalEquiv (q : I → ZMod N) (l : J → ZMod N) :=
  equiv (diagonal q) (diagonal l) (finiteBasis I) (finiteBasis J)
    (q ∘ (Fintype.equivFin I).symm) (l ∘ (Fintype.equivFin J).symm)
    (finite_weights q) (finite_weights l)

theorem diagonal_allowed_iff (q : I → ZMod N) (l : J → ZMod N) :
    SelectionCriteria.Allowed (QqqlExteriorCompleteness.Sector (diagonal q) (diagonal l)) ↔
      ∃ p, charge (q ∘ (Fintype.equivFin I).symm)
        (l ∘ (Fintype.equivFin J).symm) p = 0 :=
  allowed_iff _ _ _ _ _ _ (finite_weights q) (finite_weights l)

theorem diagonal_forbidden_iff (q : I → ZMod N) (l : J → ZMod N) :
    SelectionCriteria.Forbidden (QqqlExteriorCompleteness.Sector (diagonal q) (diagonal l)) ↔
      ∀ p, charge (q ∘ (Fintype.equivFin I).symm)
        (l ∘ (Fintype.equivFin J).symm) p ≠ 0 := by
  rw [SelectionCriteria.forbidden_iff_not_allowed, diagonal_allowed_iff]
  simp

end FiniteIndices
end
end GUT.QqqlDiagonalCoordinates
