import Math.LieGroups.SpecialUnitary.RankFive.DeterminantOneTorus
import Physics.StandardModel.Spectrum.SMChiralIndex
import Math.RepresentationTheory.Characters.AbelianCharge
import Math.RepresentationTheory.Characters.AbelianCharacterPolynomial
import Mathlib.Analysis.Fourier.AddCircleMulti

open Math

/-!
# Faithful charge-resolved characters in determinant-one torus coordinates

The existing namespace is retained for compatibility. No UV representation
is assumed by this evaluator.

Normalizing a raw weight removes exactly the common diagonal exponent.
The evaluator is faithful and intertwines the coefficient Weyl action with
actual coordinate permutations. Residual characters are never permuted.
-/

set_option autoImplicit false
open scoped BigOperators

namespace GUT.SU5.TorusCharacter

open Math.SU5
noncomputable section

open MaximalTorus StandardAbelianCharge FiniteAbelianChargeSectors

def rawCharacter (e : RawWeight) : Torus →* Circle where
  toFun z := ∏ i, z.val i ^ e i
  map_one' := by simp
  map_mul' z w := by simp [mul_zpow, Finset.prod_mul_distrib]

def weightCharacter (w : ReducedWeight) : Torus →* Circle := rawCharacter (rawReducedWeight w)

theorem weightCharacter_normalize (e : RawWeight) (z : Torus) :
    weightCharacter (normalizeWeight e) z = rawCharacter e z := by
  change (∏ i, z.val i ^ rawReducedWeight (normalizeWeight e) i) = _
  rw [rawReducedWeight_normalizeWeight]
  simp only [zpow_sub, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  rw [Finset.prod_zpow, z.property, one_zpow, inv_one, mul_one]
  rfl

theorem weightCharacter_permute (p : Equiv.Perm (Fin 5)) (w : ReducedWeight) (z : Torus) :
    weightCharacter (permuteReducedWeight p w) z = weightCharacter w (permute p z) := by
  rw [permuteReducedWeight, weightCharacter_normalize]
  change (∏ i, z.val i ^ rawReducedWeight w (p.symm i)) =
    ∏ i, z.val (p i) ^ rawReducedWeight w i
  simpa using (Equiv.prod_comp p (fun i => z.val i ^ rawReducedWeight w (p.symm i))).symm

theorem weightCharacter_coordinates (w : ReducedWeight) (x : UnitAddTorus (Fin 4)) :
    (weightCharacter w (ofCoordinates (fun i => AddCircle.toCircle (x i))) : ℂ) =
      UnitAddTorus.mFourier w x := by
  change ((∏ i : Fin 5, (ofCoordinates (fun j => AddCircle.toCircle (x j))).val i ^
    rawReducedWeight w i : Circle) : ℂ) = _
  rw [Fin.prod_univ_castSucc]
  simp only [ofCoordinates_castSucc, rawReducedWeight_castSucc, rawReducedWeight_last]
  simp only [zpow_zero, mul_one]
  change Circle.coeHom (∏ i : Fin 4, AddCircle.toCircle (x i) ^ w i) = _
  rw [map_prod]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_apply,
    AddCircle.toCircle_zsmul]
  rfl

theorem weightCharacter_injective : Function.Injective weightCharacter := by
  intro w v he
  have hf : UnitAddTorus.mFourier w = UnitAddTorus.mFourier v := by
    ext x
    rw [← weightCharacter_coordinates, ← weightCharacter_coordinates, he]
  have hlp : UnitAddTorus.mFourierLp (d := Fin 4) 2 w = UnitAddTorus.mFourierLp 2 v := by
    dsimp [UnitAddTorus.mFourierLp]
    rw [hf]
  exact (UnitAddTorus.orthonormal_mFourier (d := Fin 4)).linearIndependent.injective hlp

variable {H : Type*} [CommGroup H]

abbrev CombinedGroup (H : Type*) := Torus × H

def keyCharacter (key : ResolvedKey (ChargeLabel H)) : CombinedGroup H →* ℂ :=
  (Circle.coeHom.comp (weightCharacter key.1)).coprod (Circle.coeHom.comp key.2.toMul)

@[simp] theorem keyCharacter_apply (key : ResolvedKey (ChargeLabel H)) (z : Torus) (h : H) :
    keyCharacter key (z, h) = (weightCharacter key.1 z : ℂ) * (key.2.toMul h : ℂ) := rfl

theorem keyCharacter_injective : Function.Injective (keyCharacter (H := H)) := by
  rintro ⟨w, q⟩ ⟨v, r⟩ he
  apply Prod.ext
  · apply weightCharacter_injective
    ext z
    have hh := congrArg (fun f : CombinedGroup H →* ℂ => f (z, 1)) he
    simpa only [keyCharacter_apply, map_one, Circle.coe_one, mul_one] using hh
  · apply Additive.toMul.injective
    ext h
    have hh := congrArg (fun f : CombinedGroup H →* ℂ => f (1, h)) he
    simpa only [keyCharacter_apply, map_one, Circle.coe_one, one_mul] using hh

def lift (p : ResolvedCharacter (ChargeLabel H)) : AbelianActualSpectrum.Polynomial (CombinedGroup H) :=
  Finsupp.mapDomain keyCharacter p

def eval (p : ResolvedCharacter (ChargeLabel H)) (g : CombinedGroup H) : ℂ :=
  p.sum fun key n => (n : ℂ) * keyCharacter key g

@[simp] theorem eval_single (key : ResolvedKey (ChargeLabel H)) (n : ℤ) (g : CombinedGroup H) :
    eval (Finsupp.single key n) g = (n : ℂ) * keyCharacter key g := by
  classical
  simp [eval]

def evalAddHom (g : CombinedGroup H) : ResolvedCharacter (ChargeLabel H) →+ ℂ :=
  Finsupp.liftAddHom (fun key =>
    { toFun := fun n : ℤ => (n : ℂ) * keyCharacter key g
      map_zero' := by simp
      map_add' := by intros; simp [add_mul] })

theorem evalAddHom_apply (p : ResolvedCharacter (ChargeLabel H)) (g : CombinedGroup H) :
    evalAddHom g p = eval p g := rfl

theorem eval_lift (p : ResolvedCharacter (ChargeLabel H)) (g : CombinedGroup H) :
    AbelianActualSpectrum.eval (lift p) g = eval p g := by
  unfold lift AbelianActualSpectrum.eval
  rw [Finsupp.sum_mapDomain_index]
  · rfl
  · simp
  · intros; simp [add_mul]

theorem eval_injective (p q : ResolvedCharacter (ChargeLabel H))
    (he : ∀ g, eval p g = eval q g) : p = q := by
  have hl : lift p = lift q := AbelianActualSpectrum.eval_injective _ _ (by
    intro g; simpa only [eval_lift] using he g)
  ext key
  have hh := congrArg (fun f : AbelianActualSpectrum.Polynomial (CombinedGroup H) =>
    f (keyCharacter key)) hl
  simpa only [lift, Finsupp.mapDomain_apply_of_injective keyCharacter_injective] using hh

theorem eval_permute (p : ResolvedCharacter (ChargeLabel H))
    (sigma : Equiv.Perm (Fin 5)) (g : CombinedGroup H) :
    eval (permuteResolved sigma p) g = eval p (permute sigma g.1, g.2) := by
  unfold eval permuteResolved
  rw [Finsupp.sum_mapDomain_index]
  · apply Finsupp.sum_congr
    intro key _
    rcases g with ⟨z, h⟩
    simp only [permuteKey, keyCharacter_apply, weightCharacter_permute]
  · simp
  · intros; simp [add_mul]

theorem keyCharacter_neg (key : ResolvedKey (ChargeLabel H)) :
    AbelianActualSpectrum.dualCharacter (keyCharacter key) = keyCharacter (-key) := by
  have hraw (w : ReducedWeight) : rawReducedWeight (-w) = -rawReducedWeight w := by
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp
    · change rawReducedWeight (-w) (Fin.last 4) = -rawReducedWeight w (Fin.last 4)
      rw [rawReducedWeight_last, rawReducedWeight_last, neg_zero]
  ext g
  change (weightCharacter key.1 g.1⁻¹ : ℂ) * (key.2.toMul g.2⁻¹ : ℂ) =
    (weightCharacter (-key.1) g.1 : ℂ) * (key.2.toMul g.2 : ℂ)⁻¹
  rw [map_inv, map_inv]
  change (weightCharacter key.1 g.1 : ℂ)⁻¹ * (key.2.toMul g.2 : ℂ)⁻¹ = _
  congr 1
  change ((rawCharacter (rawReducedWeight key.1) g.1)⁻¹ : Circle) =
    (rawCharacter (rawReducedWeight (-key.1)) g.1 : ℂ)
  rw [hraw]
  simp only [rawCharacter, MonoidHom.coe_mk, OneHom.coe_mk, Pi.neg_apply,
    zpow_neg, Finset.prod_inv_distrib]

theorem eval_dual (p : ResolvedCharacter (ChargeLabel H)) (g : CombinedGroup H) :
    eval (StandardWeylDualTarget.dualCharacter p) g = eval p g⁻¹ := by
  unfold eval StandardWeylDualTarget.dualCharacter
  rw [Finsupp.sum_mapDomain_index]
  · apply Finsupp.sum_congr
    intro key _
    rw [← keyCharacter_neg]
    rfl
  · simp
  · intros; simp [add_mul]

theorem eval_chiralDifference (p : ResolvedCharacter (ChargeLabel H)) (g : CombinedGroup H) :
    eval (StandardWeylDualTarget.chiralDifference p) g = eval p g - eval p g⁻¹ := by
  change evalAddHom g (p - StandardWeylDualTarget.dualCharacter p) = _
  rw [map_sub, evalAddHom_apply, evalAddHom_apply, eval_dual]

end

end GUT.SU5.TorusCharacter
