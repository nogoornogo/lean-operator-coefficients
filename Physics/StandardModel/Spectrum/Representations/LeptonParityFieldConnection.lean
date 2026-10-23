import Physics.FieldTheory.Fields.SelectedFields
import Math.RepresentationTheory.Fields.JetConnection
import Physics.StandardModel.Operators.Selection.InverseCyclicSMYukawa

/-! Reconstruct the lepton-parity mass dictionary from the actual inclusion
and extraction; the final light equivalence is not a new caller premise. -/
namespace Physics.LeptonParityFieldConnection
set_option autoImplicit false
noncomputable section
open Math Representation InverseCyclicSMRealization
open scoped TensorProduct

def embed : IntertwiningMap light original :=
  IntertwiningMap.inl ℂ light (spectator.prod spectator.dual)

def extract : (Light × (ℂ × Module.Dual ℂ ℂ)) →ₗ[ℂ] Light := LinearMap.fst ℂ _ _

def dictionary : Equiv light (SelectedFields.mass mass).toRepresentation :=
  SelectedFields.massDictionary mass embed extract
    (by intro v; change (v,0) ∈ mass.radical.toSubmodule
        exact (ConstructedSpectatorRadical.mem_radical light spectator _).mpr rfl)
    (fun _ => rfl)
    (by intro u hu
        have h := (ConstructedSpectatorRadical.mem_radical light spectator u).mp hu
        exact Prod.ext rfl h.symm)

theorem dictionary_agrees (v : Light) :
    (dictionary v).val = (radicalEquiv.symm v).val := rfl

theorem extraction_covariant (g : G) (u : (SelectedFields.mass mass).toSubmodule) :
    extract (original g u) = light g (extract u) :=
  IntertwiningMap.isIntertwining _ _ dictionary.symm.toIntertwiningMap g u

/-- The global mass dictionary retains Weyl spin, while the existing species
dictionary supplies the signed coefficient alphabet and its group regrouping. -/
def leftWeyl := SelectedFields.withWeyl false dictionary

/-- The very same physical dictionary enters the actual jet syntax, with
an explicit direction action. Its finite bases are presentation choices. -/
def derivativeDictionary {I : Type*}
    (d : Representation ℂ (G × WeylSpinor.Group) (JetDirections.Direction I)) :=
  FieldJetConnection.coordinateJets leftWeyl
    (Module.Free.chooseBasis ℂ _) (Module.Free.chooseBasis ℂ _) d

def speciesWeyl (i : Fin 5) := physicalFieldEquiv i

theorem speciesWeyl_evaluation (i : Fin 5)
    (f : InvariantCoefficientTransport.Invariants
      ((DeltaLOneSignedFields.field fermionFlavor (index i)).comp coefficientGroup))
    (v : Carrier i ⊗[ℂ] WeylSpinor.Space) :
    (InvariantCoefficientTransport.alongEquiv (speciesWeyl i)).symm f v =
      f (physicalFieldEquiv i v) := rfl

def mixedInput (n m : ℕ) := FieldSelection.mixedCoefficients
  dictionary (Representation.Equiv.refl (Representation.trivial ℂ G ℂ)) n m

theorem mixed_roundtrip (n m : ℕ)
    (q : InvariantCoefficientTransport.Invariants
      ((light.exteriorPower n).tprod ((Representation.trivial ℂ G ℂ).symmetricPower m))) :
    (mixedInput n m).symm (mixedInput n m q) = q :=
  FieldSelection.mixed_roundtrip dictionary (Representation.Equiv.refl _) n m q

/-- These remain the previously constructed, statistics-correct interactions
and all-degree B1 input on this exact light carrier. -/
theorem physical_controls : mass.form ≠ 0 ∧
    InverseCyclicSMYukawa.up ≠ 0 ∧ InverseCyclicSMYukawa.down ≠ 0 ∧
    InverseCyclicSMYukawa.electron ≠ 0 ∧
    (∀ n m, ∀ f : ComposableBLSupport.Input fermionFlavor higgsFlavor
      InverseLeptonParitySelection.target n m, f = 0) :=
  ⟨spectator_mass_nonzero, InverseCyclicSMYukawa.up_nonzero,
    InverseCyclicSMYukawa.down_nonzero, InverseCyclicSMYukawa.electron_nonzero,
    all_B1_forbidden⟩
end
end Physics.LeptonParityFieldConnection
