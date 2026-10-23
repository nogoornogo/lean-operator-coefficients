import Math.LieGroups.Symplectic.QuaternionicStructure
import Math.LinearAlgebra.Quaternion.QuaternionicEigenbasis

/-! Apply the abstract paired spectral theorem to actual compact symplectic
matrices, retaining the canonical pairing of the two halves of the basis. -/

set_option autoImplicit false
open Matrix

namespace Math.CompactSymplectic

noncomputable section

abbrev Hilbert (n : ℕ) := EuclideanSpace ℂ (Index n)

def hilbertData {n : ℕ} (g : Group n) : QuaternionicSpectral.Data (Hilbert n) where
  q := (WithLp.linearEquiv 2 ℂ (Index n → ℂ)).symm.toLinearMap.comp
    ((quaternionicMap n).comp (WithLp.linearEquiv 2 ℂ (Index n → ℂ)).toLinearMap)
  square v := by
    apply WithLp.ofLp_injective
    exact quaternionicMap_square (WithLp.ofLp v)
  pairing v w := by
    change quaternionicMap n (WithLp.ofLp w) ⬝ᵥ star (quaternionicMap n (WithLp.ofLp v)) =
      star (WithLp.ofLp w ⬝ᵥ star (WithLp.ofLp v))
    simpa only [dotProduct_comm] using
      quaternionicMap_pairing (WithLp.ofLp v) (WithLp.ofLp w)
  t := (WithLp.linearEquiv 2 ℂ (Index n → ℂ)).symm.toLinearMap.comp
    ((defining n g).comp (WithLp.linearEquiv 2 ℂ (Index n → ℂ)).toLinearMap)
  unitary v w := by
    change defining n g (WithLp.ofLp w) ⬝ᵥ star (defining n g (WithLp.ofLp v)) =
      WithLp.ofLp w ⬝ᵥ star (WithLp.ofLp v)
    simpa only [dotProduct_comm] using
      defining_pairing g (WithLp.ofLp v) (WithLp.ofLp w)
  intertwines v := by
    apply WithLp.ofLp_injective
    exact quaternionicMap_intertwines g (WithLp.ofLp v)

theorem exists_paired_eigenbasis {n : ℕ} (g : Group n) :
    ∃ (b : OrthonormalBasis (Index n) ℂ (Hilbert n)) (z : Torus n),
      (∀ i, WithLp.ofLp (b (.inr i)) = quaternionicMap n (WithLp.ofLp (b (.inl i)))) ∧
      (∀ i, matrix g *ᵥ WithLp.ofLp (b (.inl i)) = (z i : ℂ) • WithLp.ofLp (b (.inl i))) := by
  obtain ⟨m, b, z, hq, ht⟩ := (hilbertData g).exists_paired_eigenbasis
  have hm : m = n := by
    have hh := Module.finrank_eq_card_basis b.toBasis
    simp only [finrank_euclideanSpace, Fintype.card_sum, Fintype.card_fin] at hh
    omega
  subst m
  refine ⟨b, z, ?_, ?_⟩
  · intro i
    exact congrArg WithLp.ofLp (hq i)
  · intro i
    exact congrArg WithLp.ofLp (ht i)

end

end Math.CompactSymplectic
