import Math.RepresentationTheory.Characters.NormalizedCharacterFamily

/-! Finite normalized presentations constructed from actual compact continuous
representations. The constituent choices need not be effective or canonical. -/

namespace Math.CompactCharacterPresentation
noncomputable section
open Representation ContinuousRepresentationScope FiniteSemisimpleDecomposition
open scoped BigOperators

universe u v w

structure Presentation (H : Type u) [Group H] [TopologicalSpace H]
    {A : Type w} (f : A → H → ℂ) where
  Index : Type u
  [indexFinite : Fintype Index]
  Carrier : Index → Type v
  [carrierNormedAdd : ∀ i, NormedAddCommGroup (Carrier i)]
  [carrierNormedSpace : ∀ i, NormedSpace ℂ (Carrier i)]
  [carrierFinite : ∀ i, FiniteDimensional ℂ (Carrier i)]
  action : ∀ i, Representation ℂ H (Carrier i)
  [irreducible : ∀ i, IsIrreducible (action i)]
  continuous : ∀ i, IsJointlyContinuous (action i)
  inequivalent : ∀ i k, i ≠ k → IsEmpty (Representation.Equiv (action i) (action k))
  coefficients : A → Index → ℤ
  character : ∀ a h, f a h = CompactVirtualCharacter.character action (coefficients a) h

attribute [instance] Presentation.indexFinite Presentation.carrierNormedAdd
  Presentation.carrierNormedSpace Presentation.carrierFinite Presentation.irreducible

section Pi
variable {H J : Type*} [Group H] [Fintype J]
  {V : J → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]

def piAction (S : ∀ j, Representation ℂ H (V j)) : Representation ℂ H (∀ j, V j) where
  toFun h := LinearMap.pi fun j => (S j h).comp (LinearMap.proj j)
  map_one' := by ext x j; simp
  map_mul' g h := by ext x j; simp [map_mul]

theorem pi_character [∀ j, FiniteDimensional ℂ (V j)]
    (S : ∀ j, Representation ℂ H (V j)) (h : H) :
    (piAction S).character h = ∑ j, (S j).character h := by
  classical
  let b := fun j => Module.finBasis ℂ (V j)
  simp only [Representation.character]
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basis b)]
  simp_rw [LinearMap.trace_eq_matrix_trace ℂ (b _)]
  simp [Matrix.trace, LinearMap.toMatrix_apply', Pi.basis_apply, Pi.basis_repr,
    piAction, Fintype.sum_sigma]
end Pi

section Decomposition
variable {H V : Type*} [Group H] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] {rho : Representation ℂ H V}

def ambientPiEquiv (D : Decomposition rho) :
    Representation.Equiv rho
      (piAction fun i => (D.subrepresentation i).toRepresentation) where
  toLinearEquiv := D.representationEquivDirectSum.toLinearEquiv.trans
    ((DFinsupp.linearEquivFunOnFintype).trans
      (LinearEquiv.piCongrRight fun i => (D.blockAmbientEquiv i).toLinearEquiv))
  isIntertwining' h := by
    apply LinearMap.ext
    intro x
    funext i
    exact (congrArg (fun z => (D.blockAmbientEquiv i) (z i))
      (IntertwiningMap.isIntertwining _ _
        D.representationEquivDirectSum.toIntertwiningMap h x)).trans
      (IntertwiningMap.isIntertwining _ _ (D.blockAmbientEquiv i).toIntertwiningMap
        h (D.representationEquivDirectSum x i))

theorem decomposition_character (D : Decomposition rho) (h : H) :
    rho.character h = ∑ i, (D.subrepresentation i).toRepresentation.character h := by
  rw [char_iso (ambientPiEquiv D)]
  exact pi_character _ h
end Decomposition

section Family
variable {H : Type u} {A : Type w} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [Fintype A]
  {V : A → Type v} [∀ a, NormedAddCommGroup (V a)] [∀ a, NormedSpace ℂ (V a)]
  [∀ a, FiniteDimensional ℂ (V a)]
  (rho : ∀ a, Representation ℂ H (V a)) (hc : ∀ a, IsJointlyContinuous (rho a))

def decomposition (a : A) : Decomposition (rho a) := by
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  exact (exists_decomposition (rho a)
    (CompactIrreducibleQuotient.semisimple (rho a) (hc a))).some

abbrev RawIndex := Σ a, Fin (decomposition rho hc a).numberOfBlocks
abbrev RawCarrier (i : RawIndex rho hc) :=
  ((decomposition rho hc i.1).subrepresentation i.2).toSubmodule
def rawAction (i : RawIndex rho hc) : Representation ℂ H (RawCarrier rho hc i) :=
  ((decomposition rho hc i.1).subrepresentation i.2).toRepresentation

instance (i : RawIndex rho hc) : IsIrreducible (rawAction rho hc i) :=
  (decomposition rho hc i.1).subrepresentation_isIrreducible i.2

omit [Fintype A] in
theorem raw_continuous (i : RawIndex rho hc) : IsJointlyContinuous (rawAction rho hc i) :=
  (hc i.1).subrepresentation _

abbrev Index := NormalizedCharacterFamily.Index (rawAction rho hc)
abbrev Carrier (i : Index rho hc) := NormalizedCharacterFamily.Carrier (rawAction rho hc) i
abbrev action (i : Index rho hc) := NormalizedCharacterFamily.action (rawAction rho hc) i

omit [Fintype A] in
theorem continuous (i : Index rho hc) : IsJointlyContinuous (action rho hc i) :=
  NormalizedCharacterFamily.continuous _ (raw_continuous rho hc) i

omit [Fintype A] in
theorem inequivalent (i k : Index rho hc) (hne : i ≠ k) :
    IsEmpty (Representation.Equiv (action rho hc i) (action rho hc k)) :=
  NormalizedCharacterFamily.inequivalent _ i k hne

def coefficients (a : A) : Index rho hc → ℤ := by
  classical
  exact NormalizedCharacterFamily.coefficients (rawAction rho hc)
    (fun i => if i.1 = a then 1 else 0)

theorem character (a : A) (h : H) :
    (rho a).character h =
      CompactVirtualCharacter.character (action rho hc) (coefficients rho hc a) h := by
  classical
  rw [coefficients, NormalizedCharacterFamily.character]
  simp only [CompactVirtualCharacter.character, Fintype.sum_sigma]
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul]
  simpa [Finset.sum_ite_irrel, rawAction] using
    decomposition_character (decomposition rho hc a) h

theorem difference (a b : A) (h : H) :
    (rho a).character h - (rho b).character h =
      CompactVirtualCharacter.character (action rho hc)
        (fun i => coefficients rho hc a i - coefficients rho hc b i) h := by
  rw [character rho hc a, character rho hc b]
  simp [CompactVirtualCharacter.character, sub_mul, Finset.sum_sub_distrib]

theorem coefficients_nonnegative (a : A) (i : Index rho hc) :
    0 ≤ coefficients rho hc a i := by
  classical
  unfold coefficients NormalizedCharacterFamily.coefficients
  exact Finset.sum_nonneg fun j _ => by
    dsimp only
    split_ifs <;> norm_num

theorem coefficients_unique (a : A) (b : Index rho hc → ℤ)
    (hb : ∀ h, (rho a).character h = CompactVirtualCharacter.character (action rho hc) b h) :
    coefficients rho hc a = b := by
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  apply CompactVirtualCharacter.character_injective _ (continuous rho hc) (inequivalent rho hc)
  funext h
  exact (character rho hc a h).symm.trans (hb h)

def normalized : Presentation.{u, v, w} H (fun a => (rho a).character) where
  Index := Index rho hc
  Carrier := Carrier rho hc
  action := action rho hc
  continuous := continuous rho hc
  inequivalent := inequivalent rho hc
  coefficients := coefficients rho hc
  character := character rho hc

end Family

end
end Math.CompactCharacterPresentation
