import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkFlavorProjection
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.Alternating.Basic
import Math.RepresentationTheory.Symmetric.SymmetricSquareDescent
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import TauCeti.Data.Fin.Basic

open Math

namespace Physics.LiSixQuarkFlavorAlternating
noncomputable section
set_option autoImplicit false
open scoped TensorProduct
open LiSixQuarkFlavorProjection SixQuarkTypedFlavor
open SixQuarkFlavorCoordinates LiSixQuarkExtension

def blockOrder : Fin 6 ≃ Fin 2 ⊕ Fin 4 where
  toFun i := ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inr 1,
    Sum.inr 2, Sum.inr 3] i
  invFun j := match j with
    | .inl i => ![0,2] i
    | .inr i => ![1,3,4,5] i
  left_inv i := by fin_cases i <;> rfl
  right_inv j := by cases j with
    | inl i => fin_cases i <;> rfl
    | inr i => fin_cases i <;> rfl

universe u
variable {H : Type*} [Group H]
variable {U D : Type u} [AddCommGroup U] [Module ℂ U]
  [AddCommGroup D] [Module ℂ D]
variable (up : Representation ℂ H U) (down : Representation ℂ H D)

abbrev BlockFlavor (j : Fin 2 ⊕ Fin 4) : Type u := match j with
  | .inl _ => U
  | .inr _ => D

instance (j : Fin 2 ⊕ Fin 4) : AddCommGroup (BlockFlavor (U := U) (D := D) j) :=
  match j with
  | .inl _ => inferInstanceAs (AddCommGroup U)
  | .inr _ => inferInstanceAs (AddCommGroup D)

instance (j : Fin 2 ⊕ Fin 4) : Module ℂ (BlockFlavor (U := U) (D := D) j) :=
  match j with
  | .inl _ => inferInstanceAs (Module ℂ U)
  | .inr _ => inferInstanceAs (Module ℂ D)

def blockLinear (j : Fin 2 ⊕ Fin 4) :
    BlockFlavor (U := U) (D := D) j →ₗ[ℂ] SlotFlavor U D (blockOrder.symm j) := by
  cases j with
  | inl i => exact match i with
      | 0 => LinearMap.id
      | 1 => LinearMap.id
  | inr i => exact match i with
      | 0 => LinearMap.id
      | 1 => LinearMap.id
      | 2 => LinearMap.id
      | 3 => LinearMap.id

def blocks (k : StatisticsHom U D up down) :
    MultilinearMap ℂ (fun _ : Fin 2 => U)
      (MultilinearMap ℂ (fun _ : Fin 4 => D) ℂ) :=
  (((MultilinearMap.domDomCongrLinearEquiv' ℂ ℂ (SlotFlavor U D) ℂ
    blockOrder) (missing up down k)).compLinearMap
      (blockLinear (U := U) (D := D))).currySum

def pack (u : Fin 2 → U) (d : Fin 4 → D) : ∀ i, SlotFlavor U D i :=
  fun i => match i with
    | 0 => u 0
    | 1 => d 0
    | 2 => u 1
    | 3 => d 1
    | 4 => d 2
    | 5 => d 3

theorem blocks_apply (k : StatisticsHom U D up down) (u : Fin 2 → U) (d : Fin 4 → D) :
    blocks up down k u d = missing up down k (pack u d) := by
  change missing up down k _ = _
  congr 1
  funext i
  fin_cases i <;> rfl

theorem down_adjacent (k : StatisticsHom U D up down) (u : Fin 2 → U)
    (d : Fin 4 → D) (i : Fin 3) :
    blocks up down k u (d ∘ Equiv.swap i.castSucc i.succ) = -blocks up down k u d := by
  have h := missing_exchange up down k (i.succ) (pack u d)
  have he : exchangeFlavor i.succ (speciesExchange U D i.succ) (pack u d) =
      pack u (d ∘ Equiv.swap i.castSucc i.succ) := by
    funext q
    fin_cases i <;> fin_cases q <;> rfl
  rw [he] at h
  rw [blocks_apply, blocks_apply]
  simpa [localSign] using h

theorem down_permutation (k : StatisticsHom U D up down) (u : Fin 2 → U)
    (p : Equiv.Perm (Fin 4)) (d : Fin 4 → D) :
    blocks up down k u (d ∘ p) = Equiv.Perm.sign p • blocks up down k u d := by
  have hp : p ∈ Submonoid.closure (Set.range fun i : Fin 3 =>
      Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    trivial
  have hall : ∀ d, blocks up down k u (d ∘ p) =
      Equiv.Perm.sign p • blocks up down k u d := by
    induction hp using Submonoid.closure_induction with
    | mem p hp =>
      obtain ⟨i,rfl⟩ := hp
      intro d
      rw [down_adjacent]
      have hn : i.castSucc ≠ i.succ := by
        intro he
        have hv := congrArg Fin.val he
        simp at hv
      rw [Equiv.Perm.sign_swap hn]
      simp [Units.smul_def]
    | one => intro d; simp
    | mul p q hp hq ihp ihq =>
      intro d
      have hc : d ∘ (p * q) = (d ∘ p) ∘ q := rfl
      rw [hc, ihq, ihp, map_mul, mul_smul]
      rw [smul_comm]
  exact hall d

def downAlternating (k : StatisticsHom U D up down) (u : Fin 2 → U) :
    D [⋀^Fin 4]→ₗ[ℂ] ℂ where
  toMultilinearMap := blocks up down k u
  map_eq_zero_of_eq' d i j he hn := by
    have h := down_permutation up down k u (Equiv.swap i j) d
    have hd : d ∘ Equiv.swap i j = d := by
      funext q
      by_cases hqi : q = i
      · subst q; simpa using he.symm
      by_cases hqj : q = j
      · subst q; simpa using he
      simp [Equiv.swap_apply_of_ne_of_ne hqi hqj]
    rw [hd, Equiv.Perm.sign_swap hn] at h
    simp only [Units.smul_def, Units.val_neg, Units.val_one, neg_one_smul] at h
    linear_combination (1 / 2 : ℂ) * h

theorem up_symmetric (k : StatisticsHom U D up down) (u : Fin 2 → U) (d : Fin 4 → D) :
    blocks up down k (u ∘ Equiv.swap 0 1) d = blocks up down k u d := by
  have h := missing_exchange up down k 0 (pack u d)
  have he : exchangeFlavor 0 (speciesExchange U D 0) (pack u d) =
      pack (u ∘ Equiv.swap 0 1) d := by
    funext i
    fin_cases i <;> rfl
  rw [he] at h
  rw [blocks_apply, blocks_apply]
  simpa [localSign] using h

def alternatingBlocks (k : StatisticsHom U D up down) :
    MultilinearMap ℂ (fun _ : Fin 2 => U) (D [⋀^Fin 4]→ₗ[ℂ] ℂ) where
  toFun := downAlternating up down k
  map_update_add' u i x y := by
    ext d
    exact congrArg (fun f => f d) ((blocks up down k).map_update_add u i x y)
  map_update_smul' u i z x := by
    ext d
    exact congrArg (fun f => f d) ((blocks up down k).map_update_smul u i z x)

def wedgeBlocks (k : StatisticsHom U D up down) :
    MultilinearMap ℂ (fun _ : Fin 2 => U) ((⋀[ℂ]^4 D) →ₗ[ℂ] ℂ) :=
  exteriorPower.alternatingMapLinearEquiv.toLinearMap.compMultilinearMap
    (alternatingBlocks up down k)

theorem wedgeBlocks_symmetric (k : StatisticsHom U D up down) :
    SymmetricSquareDescent.IsSymmetric (wedgeBlocks up down k) := by
  intro p u
  change exteriorPower.alternatingMapLinearEquiv (downAlternating up down k (u ∘ p)) =
    exteriorPower.alternatingMapLinearEquiv (downAlternating up down k u)
  congr 1
  ext d
  rcases TauCeti.perm_fin_two_eq_one_or_swap p with rfl | rfl
  · rfl
  · exact up_symmetric up down k u d

/-- The missing coefficient factors through precisely the symmetric-up and
alternating-down universal quotients, with no flavor dimension bound. -/
def missingTensor (k : StatisticsHom U D up down) :
    (Sym[ℂ]^2 U ⊗[ℂ] (⋀[ℂ]^4 D)) →ₗ[ℂ] ℂ :=
  TensorProduct.lift (SymmetricSquareDescent.lift (wedgeBlocks up down k)
    (wedgeBlocks_symmetric up down k))

theorem missingTensor_apply (k : StatisticsHom U D up down)
    (u : Fin 2 → U) (d : Fin 4 → D) :
    missingTensor up down k (SymmetricPower.tprod ℂ u ⊗ₜ[ℂ]
      exteriorPower.ιMulti ℂ 4 d) = missing up down k (pack u d) := by
  rw [missingTensor, TensorProduct.lift.tmul, SymmetricSquareDescent.lift_tprod]
  change exteriorPower.alternatingMapLinearEquiv (downAlternating up down k u)
    (exteriorPower.ιMulti ℂ 4 d) = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact blocks_apply up down k u d

theorem missingTensor_zero_iff (k : StatisticsHom U D up down) :
    missingTensor up down k = 0 ↔ missing up down k = 0 := by
  constructor
  · intro h
    ext t
    let u : Fin 2 → U := ![t 0, t 2]
    let d : Fin 4 → D := ![t 1, t 3, t 4, t 5]
    have ht : pack u d = t := by funext i; fin_cases i <;> rfl
    have he := missingTensor_apply up down k u d
    rw [h, LinearMap.zero_apply, ht] at he
    exact he.symm
  · intro h
    apply TensorProduct.ext
    apply SymmetricSquareDescent.ext
    intro u
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro d
    change missingTensor up down k
      (SymmetricPower.tprod ℂ u ⊗ₜ[ℂ] exteriorPower.ιMulti ℂ 4 d) = 0
    rw [missingTensor_apply, h]
    rfl

theorem missing_zero_of_down_finrank [FiniteDimensional ℂ D]
    (hd : Module.finrank ℂ D ≤ 3) (k : StatisticsHom U D up down) :
    missing up down k = 0 := by
  ext t
  let u : Fin 2 → U := ![t 0, t 2]
  let d : Fin 4 → D := ![t 1, t 3, t 4, t 5]
  have ht : pack u d = t := by funext i; fin_cases i <;> rfl
  have hdep : ¬ LinearIndependent ℂ d := by
    intro hi
    have hcard := hi.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hcard
    omega
  have hz := (downAlternating up down k u).map_linearDependent d hdep
  change blocks up down k u d = 0 at hz
  rw [blocks_apply, ht] at hz
  exact hz

theorem printed_values_of_down_finrank [FiniteDimensional ℂ D]
    (hd : Module.finrank ℂ D ≤ 3) (k : StatisticsHom U D up down) :
    ∀ t, SixQuarkFlavorResidualHom.homCoordinates
      (slotRepresentation U D up down) k.val t ∈ LiSixQuarkPrintedSpan.printedSpan :=
  (missing_zero_iff_printed up down k).mp (missing_zero_of_down_finrank up down hd k)

end
end Physics.LiSixQuarkFlavorAlternating
