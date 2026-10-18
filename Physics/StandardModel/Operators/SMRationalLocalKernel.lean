import Physics.StandardModel.Operators.SMFullLocalKernel
import Math.RepresentationTheory.RationalCompactTests

/-! Exact rational-coordinate local tests preserve the actual coefficient kernel. -/
namespace GUT.SMRationalLocalKernel
set_option autoImplicit false
noncomputable section
open Math Representation SMIntegralLocalWeights
open scoped TensorProduct

abbrev Index (n : ℕ) := (Fin 3 × Bool) ⊕ Bool ⊕ Unit ⊕
  (WeylRealTransvections.Index × Fin (n+1))

def tests (n : ℕ) : Index n → Group
  | .inl i => color (RationalCompactTests.color i)
  | .inr (.inl b) => weak (RationalCompactTests.weak b)
  | .inr (.inr (.inl _)) => hyper RationalCircleTests.sample
  | .inr (.inr (.inr i)) => spin (WeylRealTransvections.tests n i)

theorem card_tests (n : ℕ) : Fintype.card (Index n) = 9 + 4*(n+1) := by
  have hc : Fintype.card (Fin 3 × Bool) = 6 := by decide
  simp only [Index,Fintype.card_sum,Fintype.card_bool,Fintype.card_unit,
    WeylRealTransvections.card_tests,hc]
  omega

variable {H : Type*} [_root_.Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)
  (m : ℕ) (delta : ℤ)

theorem exhaustive : FiniteInvariantKernel.Exhaustive
    (SMIntegralLocalWeights.action flavor p m delta) (tests n) := by
  intro f hf
  let rho := SMIntegralLocalWeights.action flavor p m delta
  have hc : ∀ c x, f (rho (color c) x)=f x :=
    RationalCompactTests.color_exhaustive (rho.comp color)
      (SMIntegralLocalWeights.action_color flavor p m delta) f (fun i => hf (.inl i))
  have hw : ∀ w x, f (rho (weak w) x)=f x :=
    RationalCompactTests.weak_exhaustive (rho.comp weak)
      (SMIntegralLocalWeights.action_weak flavor p m delta) f (fun b => hf (.inr (.inl b)))
  have hh : ∀ z x, f (rho (hyper z) x)=f x :=
    RationalCircleTests.invariant rho hyper (SMIntegralLocalWeights.action_hyper flavor p m delta)
      f (hf (.inr (.inr (.inl ()))))
  have hs : ∀ s x, f (rho (spin s) x)=f x :=
    SMWeylFiniteKernel.exhaustive flavor p m delta f
      (fun i => hf (.inr (.inr (.inr i))))
  intro g x
  have he : g = color g.1.1 * weak g.1.2.1 * hyper g.1.2.2 * spin g.2 := by
    rcases g with ⟨⟨c,w,z⟩,s⟩
    simp [color,weak,hyper,spin,MonoidHom.inr_apply]
  rw [he]
  simp only [map_mul,Module.End.mul_apply]
  calc
    f (rho (color g.1.1) (rho (weak g.1.2.1)
        (rho (hyper g.1.2.2) (rho (spin g.2) x)))) =
        f (rho (weak g.1.2.1) (rho (hyper g.1.2.2) (rho (spin g.2) x))) := hc _ _
    _ = f (rho (hyper g.1.2.2) (rho (spin g.2) x)) := hw _ _
    _ = f (rho (spin g.2) x) := hh _ _
    _ = f x := hs _ _

abbrev Carrier := SMWeylFiniteKernel.Carrier flavor p m
def basis := SMWeylFiniteKernel.basis flavor p m

def matrix : Matrix (Index n × Fin (Module.finrank ℂ (Carrier flavor p m)))
    (Fin (Module.finrank ℂ (Carrier flavor p m))) ℂ :=
  FiniteInvariantKernel.matrix (SMIntegralLocalWeights.action flavor p m delta)
    (basis flavor p m) (tests n)

def constraints := FiniteInvariantKernel.constraints
  (SMIntegralLocalWeights.action flavor p m delta) (basis flavor p m) (tests n)
abbrev Kernel := LinearMap.ker (constraints flavor p m delta)

def coefficientEquiv :
    InvariantCoefficientTransport.Invariants (SMIntegralLocalWeights.action flavor p m delta)
      ≃ₗ[ℂ] Kernel flavor p m delta :=
  FiniteInvariantKernel.equiv _ (basis flavor p m) (tests n) (exhaustive flavor p m delta)

theorem allowed_iff_rank_lt :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor p m delta)) ↔
    Module.finrank ℂ (LinearMap.range (constraints flavor p m delta)) <
      Fintype.card (Fin (Module.finrank ℂ (Carrier flavor p m))) := by
  unfold constraints
  exact FiniteInvariantKernel.allowed_iff_rank_lt
    (SMIntegralLocalWeights.action flavor p m delta) (basis flavor p m) (tests n)
    (exhaustive flavor p m delta)

end
end GUT.SMRationalLocalKernel
