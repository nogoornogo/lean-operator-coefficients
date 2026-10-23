import Physics.FieldTheory.Mass.Spectrum.EquivariantMassIndex
import Physics.StandardModel.Operators.BaryonOne.Qque.QqueSpinorExterior
import Math.RepresentationTheory.Characters.CompactCharacterPresentation
import Math.RepresentationTheory.Unitary.FiniteBasisUnitaryModel

/-! A common positive copy-character index supplies an actual split constituent
in every equivariant species kernel, then a physical qque exterior coefficient. -/
namespace Physics.CommonCopyKernel
set_option autoImplicit false
noncomputable section
open Math Representation ContinuousRepresentationScope SplitRepresentationProjection
open CompactEmbeddingClassification
universe u
variable {H : Type*} {S T : Type u} [Group H]
  [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
  [NormedAddCommGroup T] [InnerProductSpace ℂ T] [FiniteDimensional ℂ T]

abbrev Family (S T : Type u) : Bool → Type u := fun b => match b with
  | false => S
  | true => T

instance familyNormedAdd (b : Bool) : NormedAddCommGroup (Family S T b) := by
  cases b <;> infer_instance
instance familyNormedSpace (b : Bool) : NormedSpace ℂ (Family S T b) := by
  cases b <;> infer_instance
instance familyFinite (b : Bool) : FiniteDimensional ℂ (Family S T b) := by
  cases b <;> infer_instance

def familyAction (s : Representation ℂ H S) (t : Representation ℂ H T) :
    ∀ b, Representation ℂ H (Family S T b)
  | false => s
  | true => t

def presentation (s : Representation ℂ H S) (t : Representation ℂ H T)
    (hs : IsJointlyContinuous s) (ht : IsJointlyContinuous t) :=
  CompactCharacterPresentation.normalized (familyAction s t)
    (by intro b; cases b; exact hs; exact ht)

def difference (s : Representation ℂ H S) (t : Representation ℂ H T)
    (hs : IsJointlyContinuous s) (ht : IsJointlyContinuous t) :=
  fun i => (presentation s t hs ht).coefficients false i -
    (presentation s t hs ht).coefficients true i

theorem difference_character (s : Representation ℂ H S) (t : Representation ℂ H T)
    (hs : IsJointlyContinuous s) (ht : IsJointlyContinuous t) (h : H) :
    s.character h - t.character h =
      CompactVirtualCharacter.character (presentation s t hs ht).action
        (difference s t hs ht) h := by
  change (familyAction s t false).character h - (familyAction s t true).character h = _
  rw [(presentation s t hs ht).character false h,
    (presentation s t hs ht).character true h]
  simp only [CompactVirtualCharacter.character, difference, Int.cast_sub,
    sub_mul, Finset.sum_sub_distrib]

theorem difference_dimension (s : Representation ℂ H S) (t : Representation ℂ H T)
    (hs : IsJointlyContinuous s) (ht : IsJointlyContinuous t) :
    CompactVirtualCharacter.dimension
      (V := (presentation s t hs ht).Carrier) (difference s t hs ht) =
      (Module.finrank ℂ S : ℤ) - Module.finrank ℂ T := by
  have he := difference_character s t hs ht 1
  rw [char_one, char_one, CompactVirtualCharacter.character_one] at he
  exact_mod_cast he.symm

variable (s : Representation ℂ H S) (t : Representation ℂ H T)
  (hs : IsJointlyContinuous s) (ht : IsJointlyContinuous t)
  (hu : IsUnitaryRepresentation t)

def leftover (M : IntertwiningMap s t) :=
  (orthogonalSubrepresentation t hu M.range).toRepresentation

theorem kernel_difference (M : IntertwiningMap s t) (h : H) :
    M.ker.toRepresentation.character h - (leftover s t hu M).character h =
      CompactVirtualCharacter.character (presentation s t hs ht).action
        (difference s t hs ht) h := by
  rw [← difference_character]
  exact EquivariantMassIndex.lightIndexCharacter_eq_source_sub_target_of_target_unitary M hu h

include hu in
theorem positive_kernel_split (M : IntertwiningMap s t)
    (i : (presentation s t hs ht).Index) (hi : 0 < difference s t hs ht i) :
    Nonempty (Split M.ker.toRepresentation ((presentation s t hs ht).action i)) := by
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  exact CompactVirtualCharacter.exists_split (presentation s t hs ht).action
    (difference s t hs ht) (presentation s t hs ht).continuous
    (presentation s t hs ht).inequivalent M.ker.toRepresentation (leftover s t hu M)
    (hs.subrepresentation M.ker)
    (ht.subrepresentation (orthogonalSubrepresentation t hu M.range))
    (kernel_difference s t hs ht hu M) i hi

include hu in
theorem exists_common_split (Mq Mu Me : IntertwiningMap s t)
    (hd : Module.finrank ℂ T < Module.finrank ℂ S) :
    ∃ i : (presentation s t hs ht).Index,
      Nontrivial ((presentation s t hs ht).Carrier i) ∧
      Nonempty (Split Mq.ker.toRepresentation ((presentation s t hs ht).action i)) ∧
      Nonempty (Split Mu.ker.toRepresentation ((presentation s t hs ht).action i)) ∧
      Nonempty (Split Me.ker.toRepresentation ((presentation s t hs ht).action i)) := by
  have hp : 0 < CompactVirtualCharacter.dimension
      (V := (presentation s t hs ht).Carrier) (difference s t hs ht) := by
    rw [difference_dimension]
    omega
  obtain ⟨i, hi, hn⟩ := CompactVirtualCharacter.exists_positive
    (difference s t hs ht) hp
  exact ⟨i, Module.finrank_pos_iff.mp hn,
    positive_kernel_split s t hs ht hu Mq i hi,
    positive_kernel_split s t hs ht hu Mu i hi,
    positive_kernel_split s t hs ht hu Me i hi⟩

include hs ht hu in
theorem kernel_physical_exterior (Mq Mu Me : IntertwiningMap s t)
    (hd : Module.finrank ℂ T < Module.finrank ℂ S) :
    QqueSpinorExterior.HasModelExterior
      (a := Mq.ker.toRepresentation) (b := Mu.ker.toRepresentation)
      (d := Me.ker.toRepresentation) := by
  obtain ⟨i, hn, ⟨sq⟩, ⟨su⟩, ⟨se⟩⟩ := exists_common_split s t hs ht hu Mq Mu Me hd
  let : Nontrivial ((presentation s t hs ht).Carrier i) := hn
  exact QqueSpinorExterior.hasModelExterior sq su se


section WithoutTargetUnitarity

abbrev TargetCopy := FiniteBasisHilbertization.Copy (Module.finBasis ℂ T)

omit [IsTopologicalGroup H] [CompactSpace H] in
theorem targetCoordinateContinuity (t : Representation ℂ H T) (ht : IsJointlyContinuous t) :
    ∀ i j, Continuous fun h => (Module.finBasis ℂ T).coord i (t h ((Module.finBasis ℂ T) j)) :=
  fun i j => ((Module.finBasis ℂ T).coord i).continuous_of_finiteDimensional.comp
    (ht.orbit ((Module.finBasis ℂ T) j))

def unitaryTarget (t : Representation ℂ H T) (ht : IsJointlyContinuous t) :
    Representation ℂ H (TargetCopy (T := T)) := by
  letI : MeasurableSpace H := borel H
  letI : BorelSpace H := ⟨rfl⟩
  exact (FiniteBasisUnitaryModel.model (Module.finBasis ℂ T) t
    (targetCoordinateContinuity t ht)).toRepresentation

def targetEquiv (t : Representation ℂ H T) (ht : IsJointlyContinuous t) :
    Representation.Equiv t (unitaryTarget t ht) := by
  letI : MeasurableSpace H := borel H
  letI : BorelSpace H := ⟨rfl⟩
  exact FiniteBasisUnitaryModel.modelEquiv (Module.finBasis ℂ T) t
    (targetCoordinateContinuity t ht)

theorem unitaryTarget_continuous (t : Representation ℂ H T) (ht : IsJointlyContinuous t) :
    IsJointlyContinuous (unitaryTarget t ht) := by
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  exact FiniteBasisUnitaryModel.model_jointlyContinuous (Module.finBasis ℂ T) t
    (targetCoordinateContinuity t ht)

theorem unitaryTarget_unitary (t : Representation ℂ H T) (ht : IsJointlyContinuous t) :
    IsUnitaryRepresentation (unitaryTarget t ht) := by
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  exact FiniteBasisUnitaryModel.model_inner (Module.finBasis ℂ T) t
    (targetCoordinateContinuity t ht)

def transportMass (t : Representation ℂ H T) (ht : IsJointlyContinuous t)
    (M : IntertwiningMap s t) := (targetEquiv t ht).toIntertwiningMap.comp M

def kernelEquiv (t : Representation ℂ H T) (ht : IsJointlyContinuous t)
    (M : IntertwiningMap s t) :
    Representation.Equiv M.ker.toRepresentation (transportMass s t ht M).ker.toRepresentation where
  toLinearEquiv := {
    toFun := fun x => ⟨x.val, by
      change targetEquiv t ht (M x.val) = 0
      have hz : M x.val = 0 := x.property
      rw [hz, map_zero]⟩
    invFun := fun x => ⟨x.val, by
      apply (targetEquiv t ht).injective
      have hz : targetEquiv t ht (M x.val) = 0 := x.property
      change (targetEquiv t ht).toLinearEquiv (M.toLinearMap x.val) =
        (targetEquiv t ht).toLinearEquiv 0
      rw [map_zero]
      change (targetEquiv t ht).toLinearEquiv (M.toLinearMap x.val) = 0 at hz
      exact hz⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
    map_add' := by intro x y; rfl
    map_smul' := by intro z x; rfl }
  isIntertwining' := by intro h; ext x; rfl

/-- The target's given metric need not be invariant. The model and transported
kernels are internal proof coordinates, and the resulting splits are original. -/
theorem exists_common_split_of_continuous (Mq Mu Me : IntertwiningMap s t)
    (hd : Module.finrank ℂ T < Module.finrank ℂ S) :
    ∃ i : (presentation s (unitaryTarget t ht) hs (unitaryTarget_continuous t ht)).Index,
      Nontrivial ((presentation s (unitaryTarget t ht) hs (unitaryTarget_continuous t ht)).Carrier i) ∧
      Nonempty (Split Mq.ker.toRepresentation
        ((presentation s (unitaryTarget t ht) hs (unitaryTarget_continuous t ht)).action i)) ∧
      Nonempty (Split Mu.ker.toRepresentation
        ((presentation s (unitaryTarget t ht) hs (unitaryTarget_continuous t ht)).action i)) ∧
      Nonempty (Split Me.ker.toRepresentation
        ((presentation s (unitaryTarget t ht) hs (unitaryTarget_continuous t ht)).action i)) := by
  have hd' : Module.finrank ℂ (TargetCopy (T := T)) < Module.finrank ℂ S := by
    rw [← (targetEquiv t ht).toLinearEquiv.finrank_eq]
    exact hd
  obtain ⟨i,hn,⟨sq⟩,⟨su⟩,⟨se⟩⟩ := exists_common_split s (unitaryTarget t ht) hs
    (unitaryTarget_continuous t ht) (unitaryTarget_unitary t ht)
    (transportMass s t ht Mq) (transportMass s t ht Mu) (transportMass s t ht Me) hd'
  exact ⟨i,hn,⟨(Split.ofEquiv (kernelEquiv s t ht Mq)).trans sq⟩,
    ⟨(Split.ofEquiv (kernelEquiv s t ht Mu)).trans su⟩,
    ⟨(Split.ofEquiv (kernelEquiv s t ht Me)).trans se⟩⟩

include hs ht in
theorem kernel_physical_exterior_of_continuous (Mq Mu Me : IntertwiningMap s t)
    (hd : Module.finrank ℂ T < Module.finrank ℂ S) :
    QqueSpinorExterior.HasModelExterior (a := Mq.ker.toRepresentation)
      (b := Mu.ker.toRepresentation) (d := Me.ker.toRepresentation) := by
  obtain ⟨i,hn,⟨sq⟩,⟨su⟩,⟨se⟩⟩ := exists_common_split_of_continuous s t hs ht Mq Mu Me hd
  let : Nontrivial ((presentation s (unitaryTarget t ht) hs
    (unitaryTarget_continuous t ht)).Carrier i) := hn
  exact QqueSpinorExterior.hasModelExterior sq su se

end WithoutTargetUnitarity

end
end Physics.CommonCopyKernel
