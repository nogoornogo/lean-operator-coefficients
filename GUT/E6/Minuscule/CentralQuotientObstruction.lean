import Math.LieGroups.E6.Minuscule.CenterThree
import GUT.E6.Minuscule.UnitaryRepresentation
import Mathlib.GroupTheory.QuotientGroup.Basic

open Math

/-! The actual 27 is nontrivial on the constructed central cube root.
It cannot be replaced by a representation of the center quotient. This
does not identify the candidate or its quotient with a named global E6. -/

set_option autoImplicit false

namespace GUT.E6.Minuscule

open Math.E6.Minuscule Math.E6
noncomputable section

theorem representation_centralScalar3 :
    representation centralScalar3 = scalarRoot3 • (1 : Module.End ℂ Hilbert27) := by
  change (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 27)
    (compactMatrix centralScalar3)).toLinearMap = _
  rw [centralScalar3_matrix, map_smul, map_one]
  rfl

theorem representation_centralScalar3_ne_one : representation centralScalar3 ≠ 1 := by
  intro h
  have ht := congrArg (LinearMap.trace ℂ Hilbert27) h
  rw [representation_centralScalar3, map_smul, LinearMap.trace_one, hilbert27_finrank] at ht
  have hz : scalarRoot3 = 1 := by
    change scalarRoot3 * (27 : ℂ) = (27 : ℂ) at ht
    linear_combination (1 / 27 : ℂ) * ht
  exact scalarRoot3_ne_one hz

theorem character_centralScalar3 : representation.character centralScalar3 = 27 * scalarRoot3 := by
  rw [Representation.character, representation_centralScalar3, map_smul,
    LinearMap.trace_one, hilbert27_finrank]
  simp [mul_comm]

theorem centralScalar3_ne_one : centralScalar3 ≠ 1 := by
  intro h
  apply representation_centralScalar3_ne_one
  rw [h, map_one]

theorem compact_center_ne_bot : Subgroup.center compactIdentityComponent ≠ ⊥ := by
  intro h
  apply centralScalar3_ne_one
  simpa [h] using centralScalar3_mem_center

/-- A concrete non-descent statement, not an assumed central character. -/
theorem representation_not_descends_center :
    ¬ ∃ rho : Representation ℂ (compactIdentityComponent ⧸
        Subgroup.center compactIdentityComponent) Hilbert27,
      representation = rho.comp (QuotientGroup.mk' (Subgroup.center compactIdentityComponent)) := by
  rintro ⟨rho, h⟩
  have he := DFunLike.congr_fun h centralScalar3
  have hz : (QuotientGroup.mk' (Subgroup.center compactIdentityComponent)) centralScalar3 = 1 :=
    (QuotientGroup.eq_one_iff _).mpr centralScalar3_mem_center
  exact representation_centralScalar3_ne_one
    (by simpa only [MonoidHom.comp_apply, hz, map_one] using he)

theorem compactCandidate_not_equiv_centerless (G : Type*) [Group G]
    (hG : Subgroup.center G = ⊥) : ¬ Nonempty (compactIdentityComponent ≃* G) := by
  rintro ⟨e⟩
  have hc : e centralScalar3 ∈ Subgroup.center G :=
    Subgroup.map_center_le_center e.surjective
      ⟨centralScalar3, centralScalar3_mem_center, rfl⟩
  have he : e centralScalar3 = 1 := by simpa [hG] using hc
  exact centralScalar3_ne_one (e.injective (he.trans e.map_one.symm))

end

end GUT.E6.Minuscule
