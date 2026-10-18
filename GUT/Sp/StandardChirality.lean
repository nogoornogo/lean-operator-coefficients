import Math.LieGroups.Symplectic.UnitaryEmbedding
import GUT.Sp.RestrictedCharacter
import GUT.Common.Chirality.SelfDualSource
import GUT.SUN.Branching.DiagonalCharacter

open Math

/-! The chosen SM -> SU(5) -> USp(2(5+k)) chain has zero gauge dual index,
so it cannot meet the positive light-target hypothesis of StandardChain.
The final adapter extends this to any supplied SU(5) -> USp(2n) map.
The arbitrary-subgroup endpoint is separate in ChiralityObstruction.
These are chirality obstructions, not assertions about decay amplitudes. -/

set_option autoImplicit false

namespace GUT.CompactSymplectic.StandardChirality

open Math.CompactSymplectic
noncomputable section

open SU5

abbrev inclusion : StandardModelEmbedding.TargetGroup →* Group 5 := specialUnitaryInclusion 5

theorem inclusion_injective : Function.Injective inclusion := specialUnitaryInclusion_injective 5

theorem inclusion_continuous : Continuous inclusion := specialUnitaryInclusion_continuous 5

theorem inclusion_torus (z : MaximalTorus.Torus) :
    inclusion (MaximalTorus.hom z) = torusHom 5 z.val :=
  specialUnitaryInclusion_diagonal (MaximalTorus.hom z) z.val rfl

theorem inclusion_torus_inverse (z : MaximalTorus.Torus) :
    inclusion (MaximalTorus.hom z⁻¹) =
      inversionElement 5 * inclusion (MaximalTorus.hom z) * (inversionElement 5)⁻¹ := by
  rw [inclusion_torus, inclusion_torus]
  exact torusHom_inverse_conjugate z.val

theorem not_model {H E : Type*} [CommGroup H] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {rho : Representation ℂ (Group 5 × H) E}
    (M : GUT.StandardChain.Model inclusion rho) : False :=
  GUT.StandardChain.SelfDualSource.not_model_of_inverse_conjugacy M
    (fun z => ⟨inversionElement 5, inclusion_torus_inverse z⟩)

def blockInclusion (k : ℕ) : StandardModelEmbedding.TargetGroup →* Math.CompactSymplectic.Group (5 + k) :=
  (specialUnitaryInclusion (5 + k)).comp (SUN.Block.inclusion 5 k)

theorem blockInclusion_injective (k : ℕ) : Function.Injective (blockInclusion k) :=
  (specialUnitaryInclusion_injective (5 + k)).comp (SUN.Block.inclusion_injective 5 k)

theorem blockInclusion_continuous (k : ℕ) : Continuous (blockInclusion k) :=
  (specialUnitaryInclusion_continuous (5 + k)).comp (SUN.Block.inclusion_continuous 5 k)

theorem blockInclusion_torus (k : ℕ) (z : MaximalTorus.Torus) :
    blockInclusion k (MaximalTorus.hom z) = torusHom (5 + k) (SUN.DiagonalCharacter.entries k z) := by
  change specialUnitaryInclusion (5 + k) (SUN.Block.inclusion 5 k (MaximalTorus.hom z)) = _
  rw [SUN.DiagonalCharacter.inclusion_diagonal]
  exact specialUnitaryInclusion_diagonal _ _ rfl

theorem blockInclusion_torus_inverse (k : ℕ) (z : MaximalTorus.Torus) :
    blockInclusion k (MaximalTorus.hom z⁻¹) =
      inversionElement (5 + k) * blockInclusion k (MaximalTorus.hom z) *
        (inversionElement (5 + k))⁻¹ := by
  rw [blockInclusion_torus, blockInclusion_torus]
  have he : SUN.DiagonalCharacter.entries k z⁻¹ = (SUN.DiagonalCharacter.entries k z)⁻¹ := by
    funext j
    obtain ⟨j, rfl⟩ := (SUN.Block.indexEquiv 5 k).surjective j
    cases j <;> simp [SUN.DiagonalCharacter.entries]
  rw [he]
  exact torusHom_inverse_conjugate _

theorem not_block_model {k : ℕ} {H E : Type*} [CommGroup H] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {rho : Representation ℂ (Math.CompactSymplectic.Group (5 + k) × H) E}
    (M : GUT.StandardChain.Model (blockInclusion k) rho) : False :=
  GUT.StandardChain.SelfDualSource.not_model_of_inverse_conjugacy M
    (fun z => ⟨inversionElement (5 + k), blockInclusion_torus_inverse k z⟩)

/-- SP-2 removes the chosen block-chain restriction. -/
theorem not_arbitrary_model {n : ℕ} {H E : Type*} [CommGroup H] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {i : StandardModelEmbedding.TargetGroup →* Group n}
    {rho : Representation ℂ (Group n × H) E}
    (M : GUT.StandardChain.Model i rho) : False :=
  GUT.StandardChain.SelfDualSource.not_model_of_inverse_conjugacy M
    (restriction_inverse_conjugate (i.comp MaximalTorus.hom))

end

end GUT.CompactSymplectic.StandardChirality
