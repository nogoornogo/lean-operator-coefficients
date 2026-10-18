import Math.RepresentationTheory.Multiplicity.CompactMultiplicityIndex
import Math.RepresentationTheory.Characters.CompactVirtualCharacter

/-! Extract a split residual constituent from a signed species index.
The opposite-species dual is an actual continuous representation. -/

namespace Math.CompactVirtualMultiplicityIndex
noncomputable section
open Representation ProductFactorization ContinuousRepresentationScope
open SplitRepresentationProjection

variable {G H E U I : Type*} [Group G] [Group H] [Fintype I]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
  [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [MeasurableSpace H] [BorelSpace H]
  {V : I → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
  (S : ∀ i, Representation ℂ H (V i)) [∀ i, IsIrreducible (S i)]
  (a : I → ℤ) (hc : ∀ i, IsJointlyContinuous (S i))
  (hn : ∀ i j, i ≠ j → IsEmpty (Representation.Equiv (S i) (S j)))

include hc hn in
theorem exists_split (tau : Representation ℂ (G × H) E) (r : Representation ℂ G U)
    (ht : IsJointlyContinuous (secondRestriction tau))
    (he : ∀ h, CompactMultiplicityIndex.index tau r h = CompactVirtualCharacter.character S a h)
    (i : I) (hi : 0 < a i) : Nonempty (Split (multiplicityRepresentation tau r) (S i)) := by
  let := CompactMultiplicityIndex.normedAddCommGroup tau r
  let := CompactMultiplicityIndex.normedSpace tau r
  let := CompactMultiplicityIndex.normedAddCommGroup tau r.dual
  let := CompactMultiplicityIndex.normedSpace tau r.dual
  let := ContinuousDual.dualNormedAddCommGroup (V := MultiplicitySpace tau r.dual)
  let := ContinuousDual.dualNormedSpace (V := MultiplicitySpace tau r.dual)
  exact CompactVirtualCharacter.exists_split S a hc hn
    (multiplicityRepresentation tau r) (multiplicityRepresentation tau r.dual).dual
    (CompactMultiplicityIndex.jointlyContinuous tau r ht)
    (ContinuousDual.jointlyContinuous_dual _
      (CompactMultiplicityIndex.jointlyContinuous tau r.dual ht)) he i hi

end
end Math.CompactVirtualMultiplicityIndex
