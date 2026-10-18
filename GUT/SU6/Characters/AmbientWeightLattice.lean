import GUT.SU6.Characters.AmbientWeylMoment
import Mathlib.Tactic

/-!
# The normalized ambient SU(6) weight lattice

An algebraic character of the determinant-one diagonal torus is an integer
six-vector modulo the common diagonal vector.  This file chooses the unique
representative whose sixth coordinate is zero, namely `Fin 5 -> Integer`.

The full symmetric group still acts on this normal form: permute all six raw
coordinates and subtract the new sixth coordinate.  We prove the action laws,
embed the normalized integer lattice injectively into rational trace-zero
weights, and lift both constructions to finite `Finsupp` characters.  This is
the algebraic bridge between a faithful Laurent model and
`AmbientWeylMoment`.
-/

open scoped BigOperators

namespace GUT
namespace AmbientWeightLattice

noncomputable section

abbrev I5 := Fin 5
abbrev I6 := Fin 6

/-- Canonical exponent vectors, with the omitted sixth exponent normalized to
zero. -/
abbrev Exponent := I5 -> ℤ

/-- Restore the omitted zero sixth coordinate. -/
def rawCoord (e : Exponent) : I6 -> ℤ :=
  Fin.snoc e 0

@[simp]
theorem rawCoord_castSucc (e : Exponent) (i : I5) :
    rawCoord e i.castSucc = e i := by
  simp [rawCoord]

@[simp]
theorem rawCoord_last (e : Exponent) :
    rawCoord e (Fin.last 5) = 0 := by
  exact Fin.snoc_last
    (α := fun _ : Fin 6 => ℤ) (p := e) (x := 0)

/-- Remove the scalar-diagonal component of a rational six-vector. -/
def center (x : I6 -> ℚ) (i : I6) : ℚ :=
  x i - (∑ j, x j) / 6

theorem center_sum_zero (x : I6 -> ℚ) :
    ∑ i, center x i = 0 := by
  simp [center, Finset.sum_sub_distrib]
  ring

theorem center_sub_const (x : I6 -> ℚ) (c : ℚ) :
    center (fun i => x i - c) = center x := by
  funext i
  simp [center, Finset.sum_sub_distrib]
  ring

theorem center_permute (sigma : Equiv.Perm I6) (x : I6 -> ℚ) :
    center (x ∘ sigma.symm) = center x ∘ sigma.symm := by
  funext i
  change x (sigma.symm i) - (∑ j, x (sigma.symm j)) / 6 =
    x (sigma.symm i) - (∑ j, x j) / 6
  rw [Equiv.sum_comp sigma.symm x]

/-- The canonical rational trace-zero representative of an integral torus
character. -/
def centeredWeight (e : Exponent) : AmbientWeylMoment.Weight where
  coord := center (fun i => (rawCoord e i : ℚ))
  sum_zero := center_sum_zero _

@[simp]
theorem centeredWeight_coord (e : Exponent) (i : I6) :
    (centeredWeight e).coord i =
      center (fun j => (rawCoord e j : ℚ)) i :=
  rfl

theorem centeredWeight_injective :
    Function.Injective centeredWeight := by
  intro e f h
  funext i
  have hi := congrArg
    (fun w : AmbientWeylMoment.Weight =>
      w.coord i.castSucc - w.coord (Fin.last 5)) h
  change
    ((rawCoord e i.castSucc : ℚ) -
        (∑ j, (rawCoord e j : ℚ)) / 6) -
      ((rawCoord e (Fin.last 5) : ℚ) -
        (∑ j, (rawCoord e j : ℚ)) / 6) =
    ((rawCoord f i.castSucc : ℚ) -
        (∑ j, (rawCoord f j : ℚ)) / 6) -
      ((rawCoord f (Fin.last 5) : ℚ) -
        (∑ j, (rawCoord f j : ℚ)) / 6) at hi
  rw [rawCoord_castSucc, rawCoord_last,
    rawCoord_castSucc, rawCoord_last] at hi
  ring_nf at hi
  exact_mod_cast hi

/-- Permute all six coordinates, then subtract the new sixth exponent to
return to canonical normal form. -/
def permuteExponent (sigma : Equiv.Perm I6) (e : Exponent) : Exponent :=
  fun i =>
    rawCoord e (sigma.symm i.castSucc) -
      rawCoord e (sigma.symm (Fin.last 5))

theorem rawCoord_permuteExponent
    (sigma : Equiv.Perm I6) (e : Exponent) (i : I6) :
    rawCoord (permuteExponent sigma e) i =
      rawCoord e (sigma.symm i) -
        rawCoord e (sigma.symm (Fin.last 5)) := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp [permuteExponent]
  · rw [rawCoord_last, sub_self]

theorem centeredWeight_permuteExponent
    (sigma : Equiv.Perm I6) (e : Exponent) :
    centeredWeight (permuteExponent sigma e) =
      AmbientWeylMoment.permuteWeight sigma (centeredWeight e) := by
  ext i
  change
    center (fun j => (rawCoord (permuteExponent sigma e) j : ℚ)) i =
      center (fun j => (rawCoord e j : ℚ)) (sigma.symm i)
  have hraw :
      (fun j => (rawCoord (permuteExponent sigma e) j : ℚ)) =
        (fun j =>
          (rawCoord e (sigma.symm j) : ℚ) -
            (rawCoord e (sigma.symm (Fin.last 5)) : ℚ)) := by
    funext j
    rw [rawCoord_permuteExponent]
    norm_cast
  rw [hraw, center_sub_const]
  exact congrFun
    (center_permute sigma (fun j => (rawCoord e j : ℚ))) i

@[simp]
theorem permuteExponent_one (e : Exponent) :
    permuteExponent 1 e = e := by
  funext i
  change rawCoord e i.castSucc - rawCoord e (Fin.last 5) = e i
  rw [rawCoord_castSucc, rawCoord_last, sub_zero]

theorem permuteExponent_mul
    (sigma tau : Equiv.Perm I6) (e : Exponent) :
    permuteExponent sigma (permuteExponent tau e) =
      permuteExponent (sigma * tau) e := by
  apply centeredWeight_injective
  calc
    centeredWeight (permuteExponent sigma (permuteExponent tau e)) =
        AmbientWeylMoment.permuteWeight sigma
          (centeredWeight (permuteExponent tau e)) :=
      centeredWeight_permuteExponent sigma _
    _ = AmbientWeylMoment.permuteWeight sigma
          (AmbientWeylMoment.permuteWeight tau (centeredWeight e)) := by
      rw [centeredWeight_permuteExponent]
    _ = AmbientWeylMoment.permuteWeight (sigma * tau)
          (centeredWeight e) := by
      ext i
      rfl
    _ = centeredWeight (permuteExponent (sigma * tau) e) :=
      (centeredWeight_permuteExponent (sigma * tau) e).symm

theorem permuteExponent_injective (sigma : Equiv.Perm I6) :
    Function.Injective (permuteExponent sigma) := by
  intro e f h
  apply centeredWeight_injective
  apply AmbientWeylMoment.permuteWeight_injective sigma
  rw [← centeredWeight_permuteExponent, ← centeredWeight_permuteExponent]
  exact congrArg centeredWeight h

/-- Normalization by a common exponent is invisible on a determinant-one
six-tuple.  This is the multiplicative pairing identity behind Weyl-compatible
Laurent evaluation. -/
theorem prod_zpow_permuteExponent
    {G : Type*} [CommGroup G]
    (z : I6 -> G) (hz : ∏ i, z i = 1)
    (sigma : Equiv.Perm I6) (e : Exponent) :
    (∏ i, z i ^ rawCoord (permuteExponent sigma e) i) =
      ∏ i, z (sigma i) ^ rawCoord e i := by
  let c : ℤ := rawCoord e (sigma.symm (Fin.last 5))
  have hshift : (∏ i, (z i ^ c)⁻¹) = 1 := by
    calc
      (∏ i, (z i ^ c)⁻¹) = (∏ i, z i ^ c)⁻¹ := by
        exact Finset.prod_inv_distrib
          (s := Finset.univ) (f := fun i => z i ^ c)
      _ = ((∏ i, z i) ^ c)⁻¹ := by
        rw [show (∏ i, z i ^ c) = (∏ i, z i) ^ c by
          simpa using Finset.prod_zpow z Finset.univ c]
      _ = 1 := by simp [hz]
  calc
    (∏ i, z i ^ rawCoord (permuteExponent sigma e) i) =
        ∏ i, z i ^ (rawCoord e (sigma.symm i) - c) := by
      apply Finset.prod_congr rfl
      intro i _hi
      rw [rawCoord_permuteExponent]
    _ = (∏ i, z i ^ rawCoord e (sigma.symm i)) *
          ∏ i, (z i ^ c)⁻¹ := by
      simp_rw [zpow_sub]
      rw [Finset.prod_mul_distrib]
    _ = ∏ i, z i ^ rawCoord e (sigma.symm i) := by
      rw [hshift, mul_one]
    _ = ∏ i, z (sigma i) ^ rawCoord e i := by
      simpa using
        (Equiv.prod_comp sigma
          (fun i => z i ^ rawCoord e (sigma.symm i))).symm

/-- A finite virtual Laurent character on the normalized ambient weight
lattice. -/
abbrev Character := Exponent →₀ ℤ

def permuteCharacter (sigma : Equiv.Perm I6) (chi : Character) : Character :=
  Finsupp.mapDomain (permuteExponent sigma) chi

def IsWeylInvariant (chi : Character) : Prop :=
  ∀ sigma : Equiv.Perm I6, permuteCharacter sigma chi = chi

@[simp]
theorem permuteCharacter_one (chi : Character) :
    permuteCharacter 1 chi = chi := by
  unfold permuteCharacter
  have h : permuteExponent (1 : Equiv.Perm I6) = id := by
    funext e
    exact permuteExponent_one e
  rw [h, Finsupp.mapDomain_id]

theorem permuteCharacter_mul
    (sigma tau : Equiv.Perm I6) (chi : Character) :
    permuteCharacter sigma (permuteCharacter tau chi) =
      permuteCharacter (sigma * tau) chi := by
  unfold permuteCharacter
  rw [← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro e _he
  exact permuteExponent_mul sigma tau e

/-- Send canonical integral exponents to their rational trace-zero weights,
without changing finite virtual multiplicities. -/
def toWeightCharacter (chi : Character) : AmbientWeylMoment.Character :=
  Finsupp.mapDomain centeredWeight chi

theorem toWeightCharacter_injective :
    Function.Injective toWeightCharacter :=
  Finsupp.mapDomain_injective centeredWeight_injective

theorem toWeightCharacter_permute
    (sigma : Equiv.Perm I6) (chi : Character) :
    toWeightCharacter (permuteCharacter sigma chi) =
      AmbientWeylMoment.permuteCharacter sigma (toWeightCharacter chi) := by
  unfold toWeightCharacter permuteCharacter AmbientWeylMoment.permuteCharacter
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro e _he
  exact centeredWeight_permuteExponent sigma e

theorem isWeylInvariant_toWeightCharacter
    {chi : Character} (hchi : IsWeylInvariant chi) :
    AmbientWeylMoment.IsWeylInvariant (toWeightCharacter chi) := by
  intro sigma
  rw [← toWeightCharacter_permute, hchi sigma]

theorem isWeylInvariant_iff_toWeightCharacter (chi : Character) :
    IsWeylInvariant chi ↔
      AmbientWeylMoment.IsWeylInvariant (toWeightCharacter chi) := by
  constructor
  · exact isWeylInvariant_toWeightCharacter
  · intro h sigma
    apply toWeightCharacter_injective
    rw [toWeightCharacter_permute, h sigma]

/-- The fifth moment written directly on canonical integral exponents. -/
def fifthMomentValue (chi : Character) (x : I6 -> ℚ) : ℚ :=
  chi.sum fun e c =>
    (c : ℚ) * (∑ i, (centeredWeight e).coord i * x i) ^ 5

theorem fifthMomentValue_toWeightCharacter
    (chi : Character) (x : I6 -> ℚ) :
    AmbientWeylMoment.fifthMomentValue (toWeightCharacter chi) x =
      fifthMomentValue chi x := by
  rw [AmbientWeylMoment.fifthMomentValue, toWeightCharacter,
    Finsupp.sum_mapDomain_index_inj centeredWeight_injective]
  rfl

theorem fifthMoment_traceZero_span
    (chi : Character) (hchi : IsWeylInvariant chi) :
    ∃ A B : ℚ, ∀ x : I6 -> ℚ, (∑ i, x i) = 0 ->
      fifthMomentValue chi x =
        A * DegreeFiveWeylInvariant.powerSumValue x 5 +
          B * (DegreeFiveWeylInvariant.powerSumValue x 2 *
            DegreeFiveWeylInvariant.powerSumValue x 3) := by
  rcases AmbientWeylMoment.fifthMoment_traceZero_span
      (toWeightCharacter chi) (isWeylInvariant_toWeightCharacter hchi) with
    ⟨A, B, hAB⟩
  exact ⟨A, B, fun x hx => by
    rw [← fifthMomentValue_toWeightCharacter]
    exact hAB x hx⟩

end
end AmbientWeightLattice
end GUT
