import Physics.StandardModel.Operators.SMGenerationCauchy
import Math.RepresentationTheory.InvariantVectorInjection
import Math.RepresentationTheory.SU2SymmetricSupport

/-! Lower-half Q/L weak constituents from independent generation blocks. -/
namespace GUT.SMGenerationSupport
set_option autoImplicit false
noncomputable section
open Math Representation SMGenerationCauchy
open scoped TensorProduct

-- Keep finite-sum constructions behind their proved interfaces when
-- specializing the structural witnesses to Q6/Q12/Q18 or L2/L4/L6.
attribute [local irreducible] TopExteriorCauchy.map SymmetricCauchy.map
  SU2SymmetricEmbeddings.omegaPower

@[reducible] local instance (V : Type*) [AddCommGroup V] [Module ℂ V] :
    AddCommGroup (V ⊗[ℂ] (Fin 3 → ℂ)) := inferInstance
@[reducible] local instance (k : ℕ) : AddCommGroup
    (Sym[ℂ]^k WeakDoubletScalars.Doublet ⊗[ℂ] Sym[ℂ]^k WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    (SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    ((SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    (WeakDoubletScalars.Doublet ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance

abbrev WeakPair (k : ℕ) := (weak.symmetricPower k).tprod (weak.symmetricPower k)
abbrev SpinPair (k : ℕ) := (spin.symmetricPower k).tprod (spin.symmetricPower k)
abbrev WeakSpin (k : ℕ) := (weak.symmetricPower k).tprod (spin.symmetricPower k)

theorem omega_invariant (k : ℕ) (g : Group) :
    SpinPair k g (SU2SymmetricEmbeddings.omegaPower k) = SU2SymmetricEmbeddings.omegaPower k :=
  SU2SymmetricEmbeddings.omegaPower_invariant k (spinProjection g)

def spinInsert (k : ℕ) : IntertwiningMap (WeakPair k) ((WeakSpin k).tprod (WeakSpin k)) :=
  (ExternalInvariantTensor.regroupPairDiagonal (weak.symmetricPower k) (weak.symmetricPower k)
    (spin.symmetricPower k) (spin.symmetricPower k)).symm.toIntertwiningMap.comp
      (InvariantVectorInjection.map (WeakPair k) (SpinPair k)
        (SU2SymmetricEmbeddings.omegaPower k) (omega_invariant k))

theorem spinInsert_injective (k : ℕ) : Function.Injective (spinInsert k) :=
  (ExternalInvariantTensor.regroupPairDiagonal (weak.symmetricPower k) (weak.symmetricPower k)
    (spin.symmetricPower k) (spin.symmetricPower k)).symm.injective.comp
      (InvariantVectorInjection.injective (WeakPair k) (SpinPair k)
        (SU2SymmetricEmbeddings.omegaPower k) (omega_invariant k)
        (SymmetricPowerOperations.biEval k k SU2SymmetricEmbeddings.phi SU2SymmetricEmbeddings.psi)
        (SU2SymmetricEmbeddings.omegaPower_evaluation k))

theorem quark_six (m : ℕ) (hm : m % 2 = 0) (hmax : m ≤ 6) :
    ∃ f : IntertwiningMap (weak.symmetricPower m) ((generations quark).exteriorPower 6),
      Function.Injective f := by
  obtain ⟨f,hf⟩ := SU2SymmetricSupport.pair 3 m hm hmax
  let g := SU2SymmetricSupport.pullback weakProjection f
  let t := (GenerationExteriorBlocks.pairMap quarkThree).comp (spinInsert 3)
  exact ⟨t.comp g,
    ((GenerationExteriorBlocks.pairMap_injective quarkThree quarkThree_injective).comp
      (spinInsert_injective 3)).comp hf⟩

theorem quark_twelve (m : ℕ) (hm : m % 2 = 0) (hmax : m ≤ 12) :
    ∃ f : IntertwiningMap (weak.symmetricPower m) ((generations quark).exteriorPower 12),
      Function.Injective f := by
  obtain ⟨f,hf⟩ := SU2SymmetricSupport.pair 6 m hm hmax
  exact ⟨(GenerationExteriorBlocks.pairMap quarkSix).comp
    (SU2SymmetricSupport.pullback weakProjection f),
      (GenerationExteriorBlocks.pairMap_injective quarkSix quarkSix_injective).comp hf⟩

theorem quark_eighteen (m : ℕ) (hm : m % 2 = 0) (hmax : m ≤ 18) :
    ∃ f : IntertwiningMap (weak.symmetricPower m) ((generations quark).exteriorPower 18),
      Function.Injective f := by
  obtain ⟨f,hf⟩ := SU2SymmetricSupport.triple 6 m (by decide) hm hmax
  refine ⟨(GenerationExteriorBlocks.tripleMap quarkSix).comp
    (SU2SymmetricSupport.pullback weakProjection f), ?_⟩
  intro x y he
  apply hf
  apply GenerationExteriorBlocks.tripleMap_injective quarkSix quarkSix_injective
  exact he

theorem lepton_two (m : ℕ) (hm : m % 2 = 0) (hmax : m ≤ 2) :
    ∃ f : IntertwiningMap (weak.symmetricPower m) ((generations lepton).exteriorPower 2),
      Function.Injective f := by
  obtain ⟨f,hf⟩ := SU2SymmetricSupport.pair 1 m hm hmax
  let g := SU2SymmetricSupport.pullback weakProjection f
  let t := (GenerationExteriorBlocks.pairMap leptonOne.toIntertwiningMap).comp (spinInsert 1)
  exact ⟨t.comp g,
    ((GenerationExteriorBlocks.pairMap_injective leptonOne.toIntertwiningMap leptonOne.injective).comp
      (spinInsert_injective 1)).comp hf⟩

theorem lepton_four (m : ℕ) (hm : m % 2 = 0) (hmax : m ≤ 4) :
    ∃ f : IntertwiningMap (weak.symmetricPower m) ((generations lepton).exteriorPower 4),
      Function.Injective f := by
  obtain ⟨f,hf⟩ := SU2SymmetricSupport.pair 2 m hm hmax
  exact ⟨(GenerationExteriorBlocks.pairMap leptonTwo).comp
    (SU2SymmetricSupport.pullback weakProjection f),
      (GenerationExteriorBlocks.pairMap_injective leptonTwo leptonTwo_injective).comp hf⟩

theorem lepton_six (m : ℕ) (hm : m % 2 = 0) (hmax : m ≤ 6) :
    ∃ f : IntertwiningMap (weak.symmetricPower m) ((generations lepton).exteriorPower 6),
      Function.Injective f := by
  obtain ⟨f,hf⟩ := SU2SymmetricSupport.triple 2 m (by decide) hm hmax
  refine ⟨(GenerationExteriorBlocks.tripleMap leptonTwo).comp
    (SU2SymmetricSupport.pullback weakProjection f), ?_⟩
  intro x y he
  apply hf
  apply GenerationExteriorBlocks.tripleMap_injective leptonTwo leptonTwo_injective
  exact he

end
end GUT.SMGenerationSupport
