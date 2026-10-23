import Physics.StandardModel.Gauge.Tensors.DipoleGaugeTensor
import Physics.FieldTheory.Spinor.Weyl.FourSameWeylCompleteness
import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DuqlOrderedCompleteness
import Physics.StandardModel.Operators.BaryonOne.Inputs.FourWeakWeylCompleteness
import Math.RepresentationTheory.Coefficients.FiniteLocalRelationCompleteness

open Math

/-! Reduced local dictionaries for the same-chirality dimension-seven families.
The charged, typed field transports and fermionic exchange quotient are separate
obligations; this module does not identify a full physical sector with this core. -/
namespace Physics.BnvSevenLocal
set_option autoImplicit false
noncomputable section
open Representation SMEpsilonTensor ExternalInvariantTensor ExternalInvariantFactorization
open scoped TensorProduct

def colorRepresentation :=
  ((SmallSpecialUnitary.defining 3).tprod (SmallSpecialUnitary.defining 3)).tprod
    (SmallSpecialUnitary.defining 3)

def colorPairing : IntertwiningMap colorRepresentation
    (Representation.trivial ℂ (Matrix.specialUnitaryGroup (Fin 3) ℂ) ℂ) where
  toLinearMap := colorTensor
  isIntertwining' g := by
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext; intro a
    apply LinearMap.ext; intro b
    apply LinearMap.ext; intro c
    exact eps3_invariant _ g.prop.2 a b c

def colorProbe := (colorBasis 0 ⊗ₜ[ℂ] colorBasis 1) ⊗ₜ[ℂ] colorBasis 2

theorem color_unique (f : IntertwiningMap colorRepresentation
    (Representation.trivial ℂ (Matrix.specialUnitaryGroup (Fin 3) ℂ) ℂ)) :
    f = f colorProbe • colorPairing := by
  let k := TensorProduct.curry (TensorProduct.curry f.toLinearMap)
  have hk := SMEpsilonUniqueness.color_unique k (by
    intro g a b c
    exact IntertwiningMap.isIntertwining _ _ f g ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c))
  apply IntertwiningMap.ext
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply LinearMap.ext; intro a
  apply LinearMap.ext; intro b
  apply LinearMap.ext; intro c
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun hk a) b) c

def gaugeRepresentation := external colorRepresentation DipoleGaugeTensor.singletRepresentation
def gaugePairing := coefficient colorPairing DipoleGaugeTensor.singlet
def gaugeProbe := colorProbe ⊗ₜ[ℂ] DipoleGaugeTensor.singletWitness

theorem gauge_unique (f : Coefficient colorRepresentation DipoleGaugeTensor.singletRepresentation) :
    f = f gaugeProbe • gaugePairing :=
  NormalizedInvariantFactor.product_unique _ _ _ _ _ _ color_unique
    DipoleGaugeTensor.singlet_unique f

def representation := external gaugeRepresentation (FourSameWeylCompleteness.representation true)
abbrev LocalCoefficient := IntertwiningMap representation
  (Representation.trivial ℂ _ ℂ)
def pairing (i : Fin 2) := coefficient gaugePairing (FourSameWeylCompleteness.basisPairing true i)
def probe (i : Fin 2) := gaugeProbe ⊗ₜ[ℂ] FourSameWeylCompleteness.probe i

theorem gauge_normalized : gaugePairing gaugeProbe = 1 := by
  change colorPairing colorProbe * DipoleGaugeTensor.singlet DipoleGaugeTensor.singletWitness = 1
  simp [colorPairing, colorProbe, DipoleGaugeTensor.singlet_normalized]

theorem pairing_probe (i j : Fin 2) : pairing i (probe j) = if i = j then 1 else 0 := by
  change gaugePairing gaugeProbe *
    FourSameWeylCompleteness.basisPairing true i (FourSameWeylCompleteness.probe j) = _
  rw [gauge_normalized, one_mul, FourSameWeylCompleteness.basisPairing_probe]

theorem reconstruction (f : LocalCoefficient) : f = ∑ i, f (probe i) • pairing i :=
  FiniteInvariantFactor.product_left_line gaugeRepresentation
    (FourSameWeylCompleteness.representation true) gaugePairing gaugeProbe gauge_unique
    _ _ (FourSameWeylCompleteness.basisPairing_formula true) f

def coordinates : LocalCoefficient ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun f i := f (probe i)
  invFun c := ∑ i, c i • pairing i
  left_inv f := (reconstruction f).symm
  right_inv c := by
    funext j
    change (∑ i, c i • pairing i) (probe j) = c j
    rw [IntertwiningMap.sum_apply]
    change (∑ i, c i * pairing i (probe j)) = c j
    simp [pairing_probe]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Two-left/two-right spin contraction, with the two weak-doublet core. -/
def mixedRepresentation := external gaugeRepresentation DuqlOrderedCompleteness.spin
def mixedPairing := coefficient gaugePairing DuqlOrderedCompleteness.spinContraction
def mixedProbe := gaugeProbe ⊗ₜ[ℂ] DuqlOrderedCompleteness.spinWitness

theorem mixed_unique (f : IntertwiningMap mixedRepresentation
    (Representation.trivial ℂ _ ℂ)) : f = f mixedProbe • mixedPairing :=
  NormalizedInvariantFactor.product_unique _ _ _ _ _ _ gauge_unique
    DuqlOrderedCompleteness.spin_unique f

def fourWeakGaugeRepresentation := external colorRepresentation FourWeakWeylCompleteness.weakRepresentation
def fourWeakGaugePairing (i : Fin 2) := coefficient colorPairing (FourWeakWeylCompleteness.weakPairing i)
def fourWeakGaugeProbe (i : Fin 2) := colorProbe ⊗ₜ[ℂ] FourSameWeylCompleteness.probe i

theorem fourWeakGauge_reconstruction (f : IntertwiningMap fourWeakGaugeRepresentation
    (Representation.trivial ℂ _ ℂ)) :
    f = ∑ i, f (fourWeakGaugeProbe i) • fourWeakGaugePairing i :=
  FiniteInvariantFactor.product_left_line _ _ colorPairing colorProbe color_unique
    _ _ FourWeakWeylCompleteness.weak_formula f

/-- Two-left/two-right spin contraction, with the four weak-doublet core. -/
def mixedFourWeakRepresentation := external fourWeakGaugeRepresentation DuqlOrderedCompleteness.spin
def mixedFourWeakPairing (i : Fin 2) :=
  coefficient (fourWeakGaugePairing i) DuqlOrderedCompleteness.spinContraction
def mixedFourWeakProbe (i : Fin 2) :=
  fourWeakGaugeProbe i ⊗ₜ[ℂ] DuqlOrderedCompleteness.spinWitness

theorem mixedFourWeak_reconstruction (f : IntertwiningMap mixedFourWeakRepresentation
    (Representation.trivial ℂ _ ℂ)) :
    f = ∑ i, f (mixedFourWeakProbe i) • mixedFourWeakPairing i :=
  FiniteInvariantFactor.product_right_line _ _ _ _ fourWeakGauge_reconstruction
    _ _ DuqlOrderedCompleteness.spin_unique f

theorem spin_normalized : DuqlOrderedCompleteness.spinContraction
    DuqlOrderedCompleteness.spinWitness = 1 := by
  norm_num [DuqlOrderedCompleteness.spinContraction, DuqlOrderedCompleteness.spinSwap,
    DuqlOrderedCompleteness.spinWitness, WeylSpinor.four, WeylSpinor.epsilonLeft,
    WeylSpinor.epsilonRight, eps2, weakBasis]

theorem mixed_normalized : mixedPairing mixedProbe = 1 := by
  change gaugePairing gaugeProbe * DuqlOrderedCompleteness.spinContraction
    DuqlOrderedCompleteness.spinWitness = 1
  rw [gauge_normalized, spin_normalized, mul_one]

theorem mixedFourWeak_pairing_probe (i j : Fin 2) :
    mixedFourWeakPairing i (mixedFourWeakProbe j) = if i = j then 1 else 0 := by
  change (colorPairing colorProbe * FourWeakWeylCompleteness.weakPairing i
    (FourSameWeylCompleteness.probe j)) * DuqlOrderedCompleteness.spinContraction
      DuqlOrderedCompleteness.spinWitness = _
  have hc : colorPairing colorProbe = 1 := by simp [colorPairing, colorProbe]
  rw [hc, spin_normalized, mul_one, one_mul, FourWeakWeylCompleteness.weak_probe]

variable {R X : Type*} [Group R] [AddCommGroup X] [Module ℂ X]

def sameFlavorEquiv (x : Representation ℂ R X) : Coefficient representation x ≃ₗ[ℂ]
    (Fin 2 → IntertwiningMap x (Representation.trivial ℂ R ℂ)) :=
  FiniteInvariantFactor.equiv _ x pairing probe pairing_probe reconstruction

def mixedFlavorEquiv (x : Representation ℂ R X) : Coefficient mixedRepresentation x ≃ₗ[ℂ]
    IntertwiningMap x (Representation.trivial ℂ R ℂ) :=
  NormalizedInvariantFactor.equiv _ x mixedPairing mixedProbe mixed_normalized mixed_unique

def mixedFourWeakFlavorEquiv (x : Representation ℂ R X) :
    Coefficient mixedFourWeakRepresentation x ≃ₗ[ℂ]
      (Fin 2 → IntertwiningMap x (Representation.trivial ℂ R ℂ)) :=
  FiniteInvariantFactor.equiv _ x mixedFourWeakPairing mixedFourWeakProbe
    mixedFourWeak_pairing_probe mixedFourWeak_reconstruction

variable {J : Type*}

/-- A complete local core descends through supplied compatible exchange maps.
This consumer requires actual field exchanges, not an extra spanning premise. -/
def sameStatisticsEquiv (x : Representation ℂ R X)
    (localExchange : J → Representation.Equiv representation representation)
    (flavorExchange : J → Representation.Equiv x x) (sign : J → ℂ) :=
  FiniteLocalRelationCompleteness.equiv representation x pairing probe
    pairing_probe reconstruction localExchange flavorExchange sign

def mixedFourWeakStatisticsEquiv (x : Representation ℂ R X)
    (localExchange : J → Representation.Equiv mixedFourWeakRepresentation mixedFourWeakRepresentation)
    (flavorExchange : J → Representation.Equiv x x) (sign : J → ℂ) :=
  FiniteLocalRelationCompleteness.equiv mixedFourWeakRepresentation x
    mixedFourWeakPairing mixedFourWeakProbe mixedFourWeak_pairing_probe
    mixedFourWeak_reconstruction localExchange flavorExchange sign

end
end Physics.BnvSevenLocal
