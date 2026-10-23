import Physics.StandardModel.Spectrum.Representations.ExactSMSpectrum
import Physics.StandardModel.Spectrum.Mass.LightSMSpeciesIndex

open Math

/-! Canonical residual targets from SM multiplicity spaces. The exact spectrum
hypothesis forgets H entirely; H acts on these spaces by postcomposition. -/

namespace Physics.ExactSMResidualSpectrum
noncomputable section
open Representation ProductFactorization StandardSMGaugeTensor SMEpsilonTensor
open ContinuousRepresentationScope

abbrev Carrier : Fin 5 → Type :=
  ![Quark, Module.Dual ℂ Color, Module.Dual ℂ Color, Weak, Module.Dual ℂ ℂ]

instance carrierAdd : (i : Fin 5) → AddCommGroup (Carrier i)
  | 0 => inferInstanceAs (AddCommGroup Quark)
  | 1 => inferInstanceAs (AddCommGroup (Module.Dual ℂ Color))
  | 2 => inferInstanceAs (AddCommGroup (Module.Dual ℂ Color))
  | 3 => inferInstanceAs (AddCommGroup Weak)
  | 4 => inferInstanceAs (AddCommGroup (Module.Dual ℂ ℂ))

instance carrierModule : (i : Fin 5) → Module ℂ (Carrier i)
  | 0 => inferInstanceAs (Module ℂ Quark)
  | 1 => inferInstanceAs (Module ℂ (Module.Dual ℂ Color))
  | 2 => inferInstanceAs (Module ℂ (Module.Dual ℂ Color))
  | 3 => inferInstanceAs (Module ℂ Weak)
  | 4 => inferInstanceAs (Module ℂ (Module.Dual ℂ ℂ))

instance carrierFinite : (i : Fin 5) → FiniteDimensional ℂ (Carrier i)
  | 0 => inferInstanceAs (FiniteDimensional ℂ Quark)
  | 1 => inferInstanceAs (FiniteDimensional ℂ (Module.Dual ℂ Color))
  | 2 => inferInstanceAs (FiniteDimensional ℂ (Module.Dual ℂ Color))
  | 3 => inferInstanceAs (FiniteDimensional ℂ Weak)
  | 4 => inferInstanceAs (FiniteDimensional ℂ (Module.Dual ℂ ℂ))

def gauge : (i : Fin 5) → Representation ℂ GaugeGroup (Carrier i)
  | 0 => quark
  | 1 => upRight.dual
  | 2 => downRight.dual
  | 3 => lepton
  | 4 => electronRight.dual

variable {H V : Type*} [Group H] [NormedAddCommGroup V] [NormedSpace ℂ V]
  (tau : Representation ℂ (GaugeGroup × H) V)

abbrev TargetSpace (i : Fin 5) := MultiplicitySpace tau (gauge i)
abbrev target (i : Fin 5) := multiplicityRepresentation tau (gauge i)

variable [FiniteDimensional ℂ V]

theorem index_eq_character_of_opposite_zero {U : Type*}
    [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    (r : Representation ℂ GaugeGroup U)
    (hz : Module.finrank ℂ (MultiplicitySpace tau r.dual) = 0) (h : H) :
    (multiplicityRepresentation tau r).character h -
        (multiplicityRepresentation tau r.dual).dual.character h =
      (multiplicityRepresentation tau r).character h := by
  let : Subsingleton (MultiplicitySpace tau r.dual) :=
    (Module.finrank_zero_iff).mp hz
  have he : (multiplicityRepresentation tau r.dual).dual h = 0 := Subsingleton.elim _ _
  simp only [Representation.character, he, map_zero, sub_zero]

omit [FiniteDimensional ℂ V] in
theorem target_finrank {n s : ℕ}
    (hs : ExactSMSpectrum.HasSpectrum (firstRestriction tau) n s) :
    Module.finrank ℂ (TargetSpace tau 0) = n ∧
    Module.finrank ℂ (TargetSpace tau 1) = n ∧
    Module.finrank ℂ (TargetSpace tau 4) = n :=
  ExactSMSpectrum.exact_species_multiplicities hs

theorem target_nontrivial {n s : ℕ}
    (hs : ExactSMSpectrum.HasSpectrum (firstRestriction tau) n s) (hn : 0 < n) :
    Nontrivial (TargetSpace tau 0) := by
  apply (Module.finrank_pos_iff (R := ℂ)).mp
  rw [(target_finrank tau hs).1]
  exact hn

section Normed

@[instance_reducible]
def targetNormedAddCommGroup (i : Fin 5) : NormedAddCommGroup (TargetSpace tau i) :=
  CompactMultiplicityIndex.normedAddCommGroup tau (gauge i)

@[instance_reducible]
def targetNormedSpace (i : Fin 5) :
    letI := targetNormedAddCommGroup tau i
    NormedSpace ℂ (TargetSpace tau i) :=
  CompactMultiplicityIndex.normedSpace tau (gauge i)

theorem target_continuous [TopologicalSpace H]
    (hc : IsJointlyContinuous (secondRestriction tau)) (i : Fin 5) :
    letI := targetNormedAddCommGroup tau i
    letI := targetNormedSpace tau i
    IsJointlyContinuous (target tau i) :=
  CompactMultiplicityIndex.jointlyContinuous tau (gauge i) hc

theorem species_indices {n s : ℕ}
    (hs : ExactSMSpectrum.HasSpectrum (firstRestriction tau) n s) (h : H) :
    CompactMultiplicityIndex.index tau quark h = (target tau 0).character h ∧
    CompactMultiplicityIndex.index tau upRight.dual h = (target tau 1).character h ∧
    CompactMultiplicityIndex.index tau electronRight.dual h = (target tau 4).character h := by
  obtain ⟨hq, hu, he⟩ := ExactSMSpectrum.exact_opposite_multiplicities hs
  exact ⟨index_eq_character_of_opposite_zero tau quark hq h,
    index_eq_character_of_opposite_zero tau upRight.dual hu h,
    index_eq_character_of_opposite_zero tau electronRight.dual he h⟩

end Normed

section Source
variable {G E : Type*} [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : SU5.MaximalTorus.Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : InvariantWeylMass.SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (D : LightSMAction.Compatible j rho B)

/-- The three species-index equations are derived from an SM-only spectrum.
The companion `ExactSMFourWeightTarget` derives the four-weight equations. -/
theorem has_species_target {n s : ℕ}
    (hs : ExactSMSpectrum.HasSpectrum (firstRestriction D.action) n s) :
    letI := fun i => targetNormedAddCommGroup D.action i
    letI := fun i => targetNormedSpace D.action i
    LightSMSpeciesIndex.HasTarget j rho B D (target D.action) := by
  let := fun i => targetNormedAddCommGroup D.action i
  let := fun i => targetNormedSpace D.action i
  exact ⟨fun h => (species_indices D.action hs h).1,
    fun h => (species_indices D.action hs h).2.1,
    fun h => (species_indices D.action hs h).2.2⟩

end Source
end
end Physics.ExactSMResidualSpectrum
