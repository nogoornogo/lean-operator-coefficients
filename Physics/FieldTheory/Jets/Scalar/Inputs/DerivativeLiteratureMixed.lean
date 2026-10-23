import Physics.FieldTheory.Jets.Lorentz.LorentzJetIBP
import Math.RepresentationTheory.Lagrangian.LagrangianInput

/-! Bounded literal/sign checks for 2005.00008v3 (4.24).
These are off-shell mixed polynomials and actual IBP; a physical
two and four component dictionary and invariant basis are not asserted. -/
namespace Physics.DerivativeLiteratureMixed
set_option autoImplicit false
noncomputable section
open Math MixedJetAlgebra Representation
abbrev Label := Bool × Fin 2
abbrev A := MixedJetAlgebra.Algebra Label Label (Fin 4)
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance
def psi (c : Bool) (a : Fin 2) : A := odd ((c,a),0)
def h (c : Bool) (a : Fin 2) : A := even ((c,a),0)
abbrev D := totalDerivative (F := Label) (B := Label) (I := Fin 4)
def sigma (i : Fin 4) := LorentzDirections.pauli (Pi.single i 1)
def current (i : Fin 4) : A := ∑ a, ∑ b, sigma i a b • (psi false a*psi true b)
def reversed (i : Fin 4) : A := ∑ a, ∑ b, sigma i a b • (psi true b*psi false a)
def rho : A := h true 0*h false 0+h true 1*h false 1
def higgsCurrent (i : Fin 4) : A :=
  (h true 0*D i (h false 0)-D i (h true 0)*h false 0)+
  (h true 1*D i (h false 1)-D i (h true 1)*h false 1)
def candidate : A := Complex.I • ∑ i, current i*higgsCurrent i*rho

theorem odd_swap (a b : Fin 2) : psi false a*psi true b = -(psi true b*psi false a) := by
  change odd ((false,a),0)*odd (B := Label) ((true,b),0) = _
  have hs := MixedJetParity.odd_slide (I := Fin 4) ((false,a),0) (odd (B := Label) ((true,b),0))
  rw [MixedJetParity.involute_odd] at hs
  exact hs.trans (neg_mul _ _)

theorem current_reorder (i : Fin 4) : current i = -reversed i := by
  simp only [current,reversed,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [odd_swap,smul_neg]

def divergence : (Fin 4 →₀ A) →ₗ[ℂ] A := Finsupp.lsum ℂ D
def input : DerivativeInterface.Input Unit A where
  action := trivial ℂ Unit A
  relations := divergence.range
  stable _ _ hp := hp

theorem ibp (f : input.Coefficient) (i : Fin 4) (p q : A) :
    f.val (p*D i q) = -f.val (D i p*q) := by
  have hm : D i (p*q) ∈ input.relations :=
    ⟨Finsupp.single i (p*q), Finsupp.lsum_single ℂ _ i (p*q)⟩
  have hz := f.property hm
  change f.val (D i (p*q)) = 0 at hz
  rw [MixedJetAlgebra.totalDerivative_mul,map_add] at hz
  exact eq_neg_of_add_eq_zero_right hz

theorem current_ibp (f : input.Coefficient) (i : Fin 4) (a : Fin 2) :
    f.val ((current i*h true a*rho)*D i (h false a)) =
      -f.val (D i (current i*h true a*rho)*h false a) := ibp f i _ _

theorem candidate_extraction (f : input.Coefficient) :
    input.coefficientEquiv f (input.projection candidate) = f.val candidate := rfl

end
end Physics.DerivativeLiteratureMixed
