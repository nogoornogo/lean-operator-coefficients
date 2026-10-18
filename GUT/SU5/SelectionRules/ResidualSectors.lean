import GUT.SU5.SelectionRules.MatterSource
import Math.RepresentationTheory.Characters.UnitaryCharacterSectors
import Mathlib.Analysis.CStarAlgebra.Matrix

open Math

/-! Actual residual characters and their full multiplicity eigenspaces. -/

set_option autoImplicit false

namespace GUT.SU5.ResidualSectors

noncomputable section

open MatterSource

variable {H : Type*} [CommGroup H] {n : ℕ}

abbrev Generations (n : ℕ) := EuclideanSpace ℂ (Fin n)

def representation (R : OrdinaryAction H n) (i : Kind) : Representation ℂ H (Generations n) where
  toFun h := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (sectorAction R i h).val).toLinearMap
  map_one' := by simp
  map_mul' h k := by simp

theorem representation_apply (R : OrdinaryAction H n) (i : Kind) (h : H)
    (v : Generations n) (a : Fin n) :
    representation R i h v a = ∑ b, (sectorAction R i h).val a b * v b := rfl

theorem representation_unitary (R : OrdinaryAction H n) (i : Kind) :
    UnitaryMultiplicity.IsUnitaryRepresentation (representation R i) := by
  intro h x y
  change inner ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (sectorAction R i h).val x)
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (sectorAction R i h).val y) = _
  apply ContinuousLinearMap.inner_map_map_of_mem_unitary
  exact Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) (sectorAction R i h).property

def sector (R : OrdinaryAction H n) (i : Kind) (chi : H →* Circle) :
    Subrepresentation (representation R i) := UnitaryCharacterSectors.sector (representation R i) chi

theorem sectors_exhaust (R : OrdinaryAction H n) (i : Kind) :
    (⨆ chi, (sector R i chi).toSubmodule) = ⊤ :=
  UnitaryCharacterSectors.iSup_sector_eq_top (representation R i) (representation_unitary R i)

theorem exists_sector (R : OrdinaryAction H n) (hn : 0 < n) (i : Kind) :
    ∃ (chi : H →* Circle) (v : Generations n), v ≠ 0 ∧
      ∀ h, representation R i h v = (chi h : ℂ) • v := by
  let : Nontrivial (Generations n) := Module.nontrivial_of_finrank_pos (R := ℂ) (by simpa using hn)
  exact UnitaryCharacterSectors.exists_character_eigenvector
    (representation R i) (representation_unitary R i)

def copy (i : Kind) (v : Generations n) : Carrier i →ₗ[ℂ] Space n where
  toFun x := PiLp.single 2 i (WithLp.toLp 2 fun a => v a • x)
  map_add' := by
    intro x y
    have he : (fun a => v a • (x + y)) = (fun a => v a • x) + (fun a => v a • y) := by
      ext a; exact smul_add _ _ _
    rw [he, WithLp.toLp_add, PiLp.single_add]
  map_smul' := by
    intro z x
    simp only [PiLp.single, RingHom.id_apply]
    have h : (fun a => v a • z • x) = z • (fun a => v a • x) := by ext a; exact smul_comm _ _ _
    rw [h, WithLp.toLp_smul, Pi.single_smul, WithLp.toLp_smul]

theorem copy_injective (i : Kind) (v : Generations n) (hv : v ≠ 0) :
    Function.Injective (copy i v) := by
  obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
    by_contra! h
    apply hv
    ext a
    exact h a
  intro x y hxy
  have h := congrArg (fun w : Space n => w i a) hxy
  simp only [copy, LinearMap.coe_mk, AddHom.coe_mk, PiLp.single_eq_same, PiLp.toLp_apply] at h
  exact (smul_right_injective _ ha) h

theorem copy_gauge (i : Kind) (v : Generations n) (g : StandardModelEmbedding.TargetGroup)
    (x : Carrier i) : gauge n g (copy i v x) = copy i v (constituent i g x) := by
  ext j a
  by_cases hij : i = j
  · subst j; simp [MatterSource.gauge, copy]
  · simp [MatterSource.gauge, copy, hij]

theorem copy_residual (R : OrdinaryAction H n) (i : Kind) (chi : H →* Circle)
    (v : Generations n) (he : ∀ h, representation R i h v = (chi h : ℂ) • v)
    (h : H) (x : Carrier i) : (R h).val.val (copy i v x) = (chi h : ℂ) • copy i v x := by
  ext j a
  rw [action_eq_multiplicity]
  by_cases hij : i = j
  · subst j
    have hev := congrArg (fun w : Generations n => w a) (he h)
    simp only [representation_apply, PiLp.smul_apply] at hev
    simp only [copy, LinearMap.coe_mk, AddHom.coe_mk, PiLp.single_eq_same,
      PiLp.toLp_apply, PiLp.smul_apply, smul_smul, ← Finset.sum_smul]
    rw [hev]
    rfl
  · simp [copy, hij]

end

end GUT.SU5.ResidualSectors
