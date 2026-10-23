import Physics.StandardModel.Operators.BaryonOne.Qque.S3QqueTensorSamples

/-! A fixed S3 dictionary with bijective neutral-Higgs flavor maps and actual
qque support. No physical mass spectrum or UV realization is asserted. -/
namespace Physics.S3YukawaCompatibleQque
set_option autoImplicit false
noncomputable section
open Math Representation SelectionCriteria
open scoped TensorProduct BigOperators
open S3QqueTensorSamples (H V q sign unit)

/-- Q, uR, dR have permutation flavor; L, eR have sign flavor. -/
def quarkFlavor : Representation ℂ H V := q
def leptonFlavor : Representation ℂ H V := sign

/-- The Higgs weak doublet is residual-neutral. -/
def higgsFlavor : Representation ℂ H (Fin 2 → ℂ) := Representation.trivial ℂ H _

@[simp] theorem higgsFlavor_apply (g : H) (x : Fin 2 → ℂ) : higgsFlavor g x = x := rfl

/-- The same invariant bijection supplies each quark flavor-map gate. -/
def quarkFlavorMap : IntertwiningMap quarkFlavor quarkFlavor := .id _
def leptonFlavorMap : IntertwiningMap leptonFlavor leptonFlavor := .id _

theorem quarkFlavorMap_bijective : Function.Bijective quarkFlavorMap :=
  Function.bijective_id

theorem leptonFlavorMap_bijective : Function.Bijective leptonFlavorMap :=
  Function.bijective_id

inductive Species where
  | Q | uR | dR | L | eR

def flavor : Species → Representation ℂ H V
  | .Q | .uR | .dR => quarkFlavor
  | .L | .eR => leptonFlavor

/-- These are neutral-Higgs flavor-map gates, not physical Yukawa matching. -/
theorem flavor_map_gates :
    (∃ f : IntertwiningMap (flavor .Q) (flavor .uR), Function.Bijective f) ∧
    (∃ f : IntertwiningMap (flavor .Q) (flavor .dR), Function.Bijective f) ∧
    (∃ f : IntertwiningMap (flavor .L) (flavor .eR), Function.Bijective f) :=
  ⟨⟨quarkFlavorMap, quarkFlavorMap_bijective⟩,
    ⟨quarkFlavorMap, quarkFlavorMap_bijective⟩,
    ⟨leptonFlavorMap, leptonFlavorMap_bijective⟩⟩

/-- Every species flavor action commutes with its independent SM gauge action. -/
theorem preserves_sm (s : Species) {X : Type*} [AddCommGroup X] [Module ℂ X]
    (r : Representation ℂ StandardSMGaugeTensor.GaugeGroup X)
    (g : StandardSMGaugeTensor.GaugeGroup) (h : H) :
    Commute ((ExternalInvariantTensor.external r (flavor s)) (g,1))
      ((ExternalInvariantTensor.external r (flavor s)) (1,h)) :=
  S3QqueTensorSamples.independent_flavor_preserves_sm r (flavor s) g h

/-- Noncommutativity survives on the actual quark carrier. -/
theorem quark_actions_noncommute :
    ¬ Commute (quarkFlavor (Equiv.swap (0 : Fin 3) 1))
      (quarkFlavor (Equiv.swap (1 : Fin 3) 2)) := by
  intro he
  have hv := congrArg (fun f : Module.End ℂ V => f (unit 0) 1) he.eq
  norm_num [quarkFlavor, Module.End.mul_apply, S3DipoleSelection.action_apply,
    unit, Pi.single_apply, Equiv.swap_apply_def] at hv

def pairCoordinate (i : Fin 3) : (V ⊗[ℂ] V) →ₗ[ℂ] ℂ :=
  TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ (LinearMap.proj i) (LinearMap.proj i))

def lastCoordinate (j : Fin 3) : (V ⊗[ℂ] V) →ₗ[ℂ] ℂ :=
  TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ (LinearMap.proj j)
    (FiniteFlavorControls.coordinateSum 3))

def term (i j : Fin 3) : ((V ⊗[ℂ] V) ⊗[ℂ] (V ⊗[ℂ] V)) →ₗ[ℂ] ℂ :=
  TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ (pairCoordinate i) (lastCoordinate j))

/-- det(ones, x*y, z) times sum(r); the product x*y is coordinatewise. -/
def coefficient : ((V ⊗[ℂ] V) ⊗[ℂ] (V ⊗[ℂ] V)) →ₗ[ℂ] ℂ :=
  term 1 2 - term 2 1 - term 0 2 + term 2 0 + term 0 1 - term 1 0

theorem coefficient_apply (x y z r : V) :
    coefficient ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] r)) =
      (x 1*y 1*z 2 - x 2*y 2*z 1 - x 0*y 0*z 2 + x 2*y 2*z 0 +
        x 0*y 0*z 1 - x 1*y 1*z 0) * (∑ i, r i) := by
  simp [coefficient, term, pairCoordinate, lastCoordinate,
    FiniteFlavorControls.coordinateSum, Fin.sum_univ_succ]
  ring

theorem coefficient_invariant (g : H) (x y z r : V) :
    coefficient ((q g x ⊗ₜ[ℂ] q g y) ⊗ₜ[ℂ] (q g z ⊗ₜ[ℂ] sign g r)) =
      coefficient ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] r)) := by
  rcases S3DipoleSelection.normal_forms g with h | h | h | h | h | h <;>
    subst g <;>
    simp [coefficient_apply, S3DipoleSelection.action_apply,
      S3QqueTensorSamples.sign_apply, S3QqueTensorSamples.signCharacter,
      map_mul, Fin.sum_univ_succ, Equiv.swap_apply_def] <;> ring_nf <;> simp

def invariantCoefficient : QquePhysicalOrderedCompleteness.Residual q q sign where
  toLinearMap := coefficient
  isIntertwining' g := by
    repeat first | apply TensorProduct.ext | apply LinearMap.ext; intro
    rename_i x y z r
    exact coefficient_invariant g x y z r

def symmetricResidual : QquePhysicalExteriorCompleteness.residualSpace q q sign :=
  ⟨invariantCoefficient, by
    intro x y z r
    change coefficient ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] r)) =
      coefficient ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] r))
    rw [coefficient_apply, coefficient_apply]
    ring⟩

theorem witness : symmetricResidual.val
    ((unit 0 ⊗ₜ[ℂ] unit 0) ⊗ₜ[ℂ] (unit 1 ⊗ₜ[ℂ] unit 0)) = 1 := by
  change coefficient _ = 1
  norm_num [coefficient_apply, unit, Pi.single_apply, Fin.sum_univ_succ]

theorem residual_nonzero : symmetricResidual ≠ 0 := by
  intro hz
  have he := witness
  rw [hz] at he
  norm_num at he

theorem allowed : Allowed (QquePhysicalExteriorCompleteness.Sector q q sign) := by
  rw [(ofEquiv (QquePhysicalExteriorCompleteness.exteriorEquiv q q sign)).allowed]
  exact ⟨symmetricResidual, residual_nonzero⟩

/-- The result uses the same dictionary as the flavor-map gates. -/
theorem allowed_dictionary : Allowed (QquePhysicalExteriorCompleteness.Sector
    (flavor .Q) (flavor .uR) (flavor .eR)) := allowed

end
end Physics.S3YukawaCompatibleQque
