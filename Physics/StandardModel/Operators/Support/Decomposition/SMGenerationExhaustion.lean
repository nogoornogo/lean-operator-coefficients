import Math.RepresentationTheory.Exterior.GenerationExteriorExhaustion
import Math.RepresentationTheory.Exterior.IndexedExteriorContent
import Physics.StandardModel.Operators.Support.Joint.SMCombinedCompactAction

/-! Complete generation-occupation reduction for each of the ten actual
signed compact SM fields, preserving color, hypercharge, weak and both
independent spins. This is a foundation for target support, not a decision
of the remaining occupation multiplicities. -/
namespace Physics.SMGenerationExhaustion
set_option autoImplicit false
noncomputable section
open Math Representation
open scoped TensorProduct

abbrev Core (s : DeltaLOneSignedInput.Species) :=
  DeltaLOneSignedFields.GaugeCarrier s ⊗[ℂ] WeylSpinor.Space

def core (s : DeltaLOneSignedInput.Species) :
    Representation ℂ SMCombinedCompactAction.Group (Core s) :=
  Representation.tprod
    ((DeltaLOneSignedFields.gauge s).comp
      (MonoidHom.fst StandardSMGaugeTensor.GaugeGroup SMCombinedCompactAction.Spin))
    ((WeylIndependentAction.spin (DeltaLOneSignedFields.rightHanded s)).comp
      (SMMixedCompactWeyl.compact.comp
        (MonoidHom.snd StandardSMGaugeTensor.GaugeGroup SMCombinedCompactAction.Spin)))

theorem actual_field (s : DeltaLOneSignedInput.Species) :
    SMCombinedCompactAction.field s=GenerationExteriorExhaustion.generations (core s) := rfl

abbrev Occupation (n : ℕ) := FiniteExteriorExhaustion.Occupation (S := Fin 3) n

def leaves (s : DeltaLOneSignedInput.Species) (n : ℕ) (c : Occupation n)
    (i : Fin 3) : ExteriorContentTree.Leaf SMCombinedCompactAction.Group where
  Carrier := Core s
  rho := core s
  degree := (c.val i).val

abbrev factor (s : DeltaLOneSignedInput.Species) (n : ℕ) (c : Occupation n) :=
  ExteriorContentTree.factor (IndexedExteriorContent.tree 2 (leaves s n c))

abbrev FactorCarrier (s : DeltaLOneSignedInput.Species) (n : ℕ) (c : Occupation n) :=
  ExteriorContentTree.Carrier (IndexedExteriorContent.tree 2 (leaves s n c))

local instance coreFinite (s : DeltaLOneSignedInput.Species) : FiniteDimensional ℂ (Core s) := by
  fin_cases s <;> dsimp [Core,DeltaLOneSignedFields.GaugeCarrier] <;> infer_instance

local instance factorFinite (s : DeltaLOneSignedInput.Species) (n : ℕ) (c : Occupation n) :
    FiniteDimensional ℂ (FactorCarrier s n c) :=
  ExteriorContentTree.carrier_finite _ (IndexedExteriorContent.finiteLeaves 2 (leaves s n c)
    (fun _ => coreFinite s))

def Fits (s : DeltaLOneSignedInput.Species) (n : ℕ) (c : Occupation n) : Prop :=
  ∀ i, (c.val i).val ≤ Module.finrank ℂ (Core s)

/-- A symbolic product formula used only to exclude overflow. No closed
dimension or multiplicity is evaluated. -/
theorem factor_dimension (s : DeltaLOneSignedInput.Species) (n : ℕ) (c : Occupation n) :
    Module.finrank ℂ (FactorCarrier s n c) =
      ∏ i, (Module.finrank ℂ (Core s)).choose (c.val i).val :=
  (ExteriorContentTree.carrier_dimension _ (IndexedExteriorContent.finiteLeaves 2 (leaves s n c)
    (fun _ => coreFinite s))).trans (IndexedExteriorContent.dimensionFormula_eq 2 (leaves s n c))

/-- This is nonzeroness of the statistical source, not invariant permission. -/
theorem source_nonzero_iff (s : DeltaLOneSignedInput.Species) (n : ℕ) (c : Occupation n) :
    (∃ x : FactorCarrier s n c, x≠0) ↔ Fits s n c := by
  rw [← Module.finrank_pos_iff_exists_ne_zero (R := ℂ),factor_dimension]
  simp only [Nat.pos_iff_ne_zero,Finset.prod_ne_zero_iff,Finset.mem_univ,true_implies,
    Nat.choose_ne_zero_iff,Fits]

/-- The factors are the three single-generation exterior powers at the
specified counts. The complete retained action is preserved. -/
def occupationEquiv (s : DeltaLOneSignedInput.Species) (n : ℕ) (c : Occupation n) :
    Representation.Equiv (factor s n c)
      (PatternExteriorSource.representation (GenerationExteriorExhaustion.fields (core s))
        (FiniteExteriorExhaustion.representative n c)) :=
  IndexedExteriorContent.wordDecomposition 2 (leaves s n c)
    (FiniteExteriorExhaustion.representative n c) (fun i =>
      congrArg Fin.val (congrFun (FiniteExteriorExhaustion.representative_counts n c) i))

variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
  (s : DeltaLOneSignedInput.Species) (n : ℕ)
  (target : Representation ℂ SMCombinedCompactAction.Group Y)

theorem exists_nonzero_occupation_iff :
    (∃ f : IntertwiningMap ((SMCombinedCompactAction.field s).exteriorPower n) target, f≠0) ↔
      ∃ c : Occupation n,
        ∃ f : IntertwiningMap
          (PatternExteriorSource.representation (GenerationExteriorExhaustion.fields (core s))
            (FiniteExteriorExhaustion.representative n c)) target, f≠0 :=
  GenerationExteriorExhaustion.exists_nonzero_occupation_iff (core s) n target

/-- Complete three-generation reduction in both directions, with arbitrary
equivariant target. Individual target occurrences on the right are still
obligations; this is not the original full q/l classification theorem. -/
theorem exists_nonzero_factor_iff :
    (∃ f : IntertwiningMap ((SMCombinedCompactAction.field s).exteriorPower n) target, f≠0) ↔
      ∃ c : Occupation n, ∃ f : IntertwiningMap (factor s n c) target, f≠0 := by
  rw [exists_nonzero_occupation_iff s n target]
  constructor
  · rintro ⟨c,f,hf⟩
    refine ⟨c,f.comp (occupationEquiv s n c).toIntertwiningMap,?_⟩
    intro he
    apply hf
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := (occupationEquiv s n c).surjective x
    exact DFunLike.congr_fun he y
  · rintro ⟨c,f,hf⟩
    refine ⟨c,f.comp (occupationEquiv s n c).symm.toIntertwiningMap,?_⟩
    intro he
    apply hf
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := (occupationEquiv s n c).symm.surjective x
    exact DFunLike.congr_fun he y

theorem nonzero_factor_fits (c : Occupation n)
    (f : IntertwiningMap (factor s n c) target) (hf : f≠0) : Fits s n c := by
  apply (source_nonzero_iff s n c).mp
  by_contra hn
  push Not at hn
  apply hf
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  rw [hn x,map_zero]
  rfl

/-- All nonzero target maps are accounted for by the finite three-count
family with total n and each count at most the single-generation capacity. -/
theorem exists_nonzero_bounded_factor_iff :
    (∃ f : IntertwiningMap ((SMCombinedCompactAction.field s).exteriorPower n) target, f≠0) ↔
      ∃ c : Occupation n, Fits s n c ∧
        ∃ f : IntertwiningMap (factor s n c) target, f≠0 := by
  rw [exists_nonzero_factor_iff s n target]
  constructor
  · rintro ⟨c,f,hf⟩
    exact ⟨c,nonzero_factor_fits s n target c f hf,f,hf⟩
  · rintro ⟨c,_,f,hf⟩
    exact ⟨c,f,hf⟩

end
end Physics.SMGenerationExhaustion
