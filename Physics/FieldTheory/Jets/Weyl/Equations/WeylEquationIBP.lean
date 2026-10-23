import Physics.FieldTheory.Jets.Weyl.Equations.WeylEquationControls
import Math.RepresentationTheory.Jets.LinearJetIBP

/-! Free left-Weyl equations in the actual mixed algebra, with scalar spectators
and inverse equivariant EOM/IBP source transport. -/
namespace Physics.WeylLinearEquation
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear Math.JetDirections
open scoped TensorProduct

def spectatorSeed : ℂ →ₗ[ℂ] Jet Unit (Fin 4) := 0
def spectatorEquations : Representation ℂ Group ℂ := Representation.trivial ℂ Group ℂ

theorem spectator_covariant (g : Group) (x : ℂ) :
    combined LorentzJetIBP.scalarField LorentzDirections.direction g (spectatorSeed x) =
      spectatorSeed (spectatorEquations g x) := by simp [spectatorSeed]

abbrev Algebra := LinearJetAlgebra.Algebra seed spectatorSeed
def projection := LinearJetAlgebra.projection seed spectatorSeed
def algebraAction := LinearJetAlgebra.action seed spectatorSeed WeylSpinor.right.dual spectatorEquations
  (LorentzJetIBP.weyl false) LorentzJetIBP.scalarField LorentzDirections.direction seed_covariant spectator_covariant

theorem equation_zero (f : Equations) :
    projection (JetFunctor.oddVector (B := Unit) (seed f)) = 0 := by
  change LinearJetAlgebra.oddProjection seed (ExteriorAlgebra.ι ℂ (seed f)) ⊗ₜ[ℂ]
    LinearJetAlgebra.evenProjection spectatorSeed 1 = 0
  rw [LinearJetAlgebra.oddProjection_ι,
    show relations.mkQ (seed f) = 0 from (Submodule.Quotient.mk_eq_zero _).mpr (LinearJetEquation.seed_mem seed f),
    map_zero, TensorProduct.zero_tmul]

theorem equation_descendant_zero (p : Symbols (Fin 4)) (f : Equations) :
    projection (JetFunctor.oddVector (B := Unit) (LinearJetEquation.multiple p (seed f))) = 0 := by
  change LinearJetAlgebra.oddProjection seed (ExteriorAlgebra.ι ℂ _) ⊗ₜ[ℂ]
    LinearJetAlgebra.evenProjection spectatorSeed 1 = 0
  rw [LinearJetAlgebra.oddProjection_ι, descendant_zero, map_zero, TensorProduct.zero_tmul]

def detect : Algebra →ₗ[ℂ] ℂ := (TensorProduct.lid ℂ ℂ).toLinearMap.comp
  (TensorProduct.map (onShellProbe.comp ExteriorAlgebra.ιInv)
    (SymmetricAlgebra.lift (0 : LinearJetEquation.Generator spectatorSeed →ₗ[ℂ] ℂ)).toLinearMap)

theorem higher_mixed_jet_survives (k : ℕ) :
    projection (JetFunctor.oddVector (B := Unit) (ofSymbols (1 : Fin 2) (MvPolynomial.X (0 : Fin 4) ^ k))) ≠ 0 := by
  intro hz
  have he := congrArg detect hz
  rw [map_zero] at he
  change detect (LinearJetAlgebra.projection seed spectatorSeed
    (ExteriorAlgebra.ι ℂ (ofSymbols (1 : Fin 2) (MvPolynomial.X (0 : Fin 4) ^ k)) ⊗ₜ[ℂ]
      (1 : MixedJetAlgebra.Even Unit (Fin 4)))) = 0 at he
  rw [LinearJetAlgebra.projection_tmul, LinearJetAlgebra.oddProjection_ι] at he
  simp only [detect, LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.lid_tmul,
    LinearEquiv.coe_coe] at he
  change onShellProbe (ExteriorAlgebra.ιInv (ExteriorAlgebra.ι ℂ
    (relations.mkQ (ofSymbols (1 : Fin 2) (MvPolynomial.X (0 : Fin 4) ^ k))))) •
      (SymmetricAlgebra.lift (0 : LinearJetEquation.Generator spectatorSeed →ₗ[ℂ] ℂ))
        (LinearJetAlgebra.evenProjection spectatorSeed 1) = 0 at he
  rw [ExteriorAlgebra.ι_leftInverse, map_one, map_one, smul_eq_mul, mul_one] at he
  change probe (ofSymbols (1 : Fin 2) (MvPolynomial.X (0 : Fin 4) ^ k)) = 0 at he
  simp [probe_ofSymbols, nullPoint] at he

theorem projection_derivative (i : Fin 4) (x : MixedJetAlgebra.Algebra (Fin 2) Unit (Fin 4)) :
    projection (MixedJetAlgebra.totalDerivative i x) =
      LinearJetAlgebra.derivative seed spectatorSeed i (projection x) :=
  LinearJetAlgebra.projection_derivative seed spectatorSeed i x

theorem finite_source (n m d : ℕ) : FiniteDimensional ℂ (LinearJetAlgebra.grade seed spectatorSeed n m d) :=
  inferInstance

def sourceEquiv (n m d : ℕ) := LinearJetAlgebra.combinedRepresentationEquiv seed spectatorSeed
  WeylSpinor.right.dual spectatorEquations (LorentzJetIBP.weyl false) LorentzJetIBP.scalarField
  LorentzDirections.direction seed_covariant spectator_covariant n m d

def coefficientEquiv (n m d : ℕ) := LinearJetAlgebra.coefficientEquiv seed spectatorSeed
  WeylSpinor.right.dual spectatorEquations (LorentzJetIBP.weyl false) LorentzJetIBP.scalarField
  LorentzDirections.direction seed_covariant spectator_covariant n m d

end
end Physics.WeylLinearEquation
