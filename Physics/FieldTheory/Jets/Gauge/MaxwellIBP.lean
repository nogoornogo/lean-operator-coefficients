import Physics.FieldTheory.Jets.Gauge.MaxwellWave
import Physics.FieldTheory.Jets.Gauge.MaxwellProbes
import Math.Algebra.Jets.LinearJetKernel
import Math.RepresentationTheory.Jets.LinearJetIBP

/-! The actual bosonic Maxwell/Bianchi algebra and equivariant EOM/IBP descent. -/
namespace Physics.AbelianFieldStrength
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear Math.JetDirections LorentzDirections
open scoped TensorProduct

def oddSeed : ℂ →ₗ[ℂ] Jet Empty (Fin 4) := 0
def oddEquations : Representation ℂ Group ℂ := Representation.trivial ℂ Group ℂ
def oddField : Representation ℂ Group (JetLinear.Field Empty) := Representation.trivial ℂ Group _

theorem odd_covariant (g : Group) (v : ℂ) :
    combined oddField direction g (oddSeed v) = oddSeed (oddEquations g v) := by simp [oddSeed]

abbrev Algebra := LinearJetAlgebra.Algebra oddSeed seed
def projection := LinearJetAlgebra.projection oddSeed seed
def algebraAction := LinearJetAlgebra.action oddSeed seed oddEquations equationAction
  oddField field direction odd_covariant seed_covariant

theorem projection_surjective : Function.Surjective projection := LinearJetAlgebra.projection_surjective _ _

theorem equation_descendant_zero (p : Symbols (Fin 4)) (x : Equations) :
    projection (JetFunctor.evenVector (F := Empty) (LinearJetEquation.multiple p (seed x))) = 0 := by
  change LinearJetAlgebra.oddProjection oddSeed 1 ⊗ₜ[ℂ]
    LinearJetAlgebra.evenProjection seed (JetLinear.linearForm (LinearJetEquation.multiple p (seed x))) = 0
  rw [LinearJetAlgebra.evenProjection_linearForm, descendant_zero, map_zero, TensorProduct.tmul_zero]

theorem projection_derivative (i : Fin 4) (x : MixedJetAlgebra.Algebra Empty Component (Fin 4)) :
    projection (MixedJetAlgebra.totalDerivative i x) =
      LinearJetAlgebra.derivative oddSeed seed i (projection x) :=
  LinearJetAlgebra.projection_derivative _ _ i x

theorem kernel_presentation : TwoSidedIdeal.ker projection = LinearJetAlgebra.descendantIdeal oddSeed seed :=
  LinearJetAlgebra.kernel_eq_descendantIdeal _ _

theorem finite_source (m d : ℕ) : FiniteDimensional ℂ (LinearJetAlgebra.grade oddSeed seed 0 m d) := inferInstance

def sourceEquiv (m d : ℕ) := LinearJetAlgebra.combinedRepresentationEquiv oddSeed seed oddEquations equationAction
  oddField field direction odd_covariant seed_covariant 0 m d

def coefficientEquiv (m d : ℕ) := LinearJetAlgebra.coefficientEquiv oddSeed seed oddEquations equationAction
  oddField field direction odd_covariant seed_covariant 0 m d

private def oddAugmentation : LinearJetAlgebra.Odd oddSeed →ₐ[ℂ] ℂ :=
  ExteriorAlgebra.lift ℂ ⟨0, by intro v; simp⟩

private def oddScalarEquiv : LinearJetAlgebra.Odd oddSeed ≃ₐ[ℂ] ℂ :=
  AlgEquiv.ofAlgHom oddAugmentation (Algebra.ofId ℂ _) (by ext) (by
    apply ExteriorAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    have hv : v = 0 := Subsingleton.elim _ _
    rw [hv]
    simp)

def evenEquiv : Algebra ≃ₐ[ℂ] SymmetricAlgebra ℂ Generator :=
  (Algebra.TensorProduct.congr oddScalarEquiv (AlgEquiv.refl : LinearJetAlgebra.Even seed ≃ₐ[ℂ] _)).trans
    (Algebra.TensorProduct.lid ℂ (SymmetricAlgebra ℂ Generator))

def algebraProbe (t : Fin 2) : Algebra →ₗ[ℂ] ℂ := (TensorProduct.lid ℂ ℂ).toLinearMap.comp
  (TensorProduct.map oddAugmentation.toLinearMap (SymmetricAlgebra.lift (onShellProbe t)).toLinearMap)

def evenJet (t : Fin 2) (k : ℕ) : Algebra :=
  1 ⊗ₜ[ℂ] SymmetricAlgebra.ι ℂ Generator (transverseJet t k)

theorem evenEquiv_evenJet (t : Fin 2) (k : ℕ) :
    evenEquiv (evenJet t k) = SymmetricAlgebra.ι ℂ Generator (transverseJet t k) := by
  simp [evenEquiv, evenJet]

theorem algebraProbe_evenJet (t s : Fin 2) (k : ℕ) : algebraProbe t (evenJet s k) = if t = s then 1 else 0 := by
  change (TensorProduct.lid ℂ ℂ)
    (oddAugmentation 1 ⊗ₜ[ℂ] (SymmetricAlgebra.lift (onShellProbe t)) (SymmetricAlgebra.ι ℂ Generator (transverseJet s k))) = _
  rw [map_one, SymmetricAlgebra.lift_ι_apply, onShellProbe_transverseJet, TensorProduct.lid_tmul]
  simp

theorem evenJet_nonzero (t : Fin 2) (k : ℕ) : evenJet t k ≠ 0 := by
  intro h
  have he := congrArg (algebraProbe t) h
  rw [algebraProbe_evenJet, ite_eq_left rfl, map_zero] at he
  exact one_ne_zero he

theorem projection_evenJet (t : Fin 2) (k : ℕ) : projection (JetFunctor.evenVector (F := Empty)
    (ofSymbols (0, transverseDirection t) (MvPolynomial.X (0 : Fin 4) ^ k))) = evenJet t k := by
  change LinearJetAlgebra.oddProjection oddSeed 1 ⊗ₜ[ℂ]
    LinearJetAlgebra.evenProjection seed (JetLinear.linearForm _) = _
  rw [map_one, LinearJetAlgebra.evenProjection_linearForm]
  rfl

theorem higher_even_jet_survives (t : Fin 2) (k : ℕ) : projection (JetFunctor.evenVector (F := Empty)
    (ofSymbols (0, transverseDirection t) (MvPolynomial.X (0 : Fin 4) ^ k))) ≠ 0 := by
  rw [projection_evenJet]
  exact evenJet_nonzero t k

end
end Physics.AbelianFieldStrength
