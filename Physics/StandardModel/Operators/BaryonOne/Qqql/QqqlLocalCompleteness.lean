import Physics.StandardModel.Operators.BaryonOne.Inputs.FourWeakWeylCompleteness
import Physics.StandardModel.Gauge.Tensors.SMEpsilonUniqueness

open Math

/-! Exhaustive qqql local factors in regrouped color/weak/Weyl coordinates.
Transport from physical SM fields (including hypercharge) is separate. -/
namespace Physics.QqqlLocalCompleteness
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SMEpsilonTensor SmallSpecialUnitary
open scoped TensorProduct

abbrev ColorGroup := Matrix.specialUnitaryGroup (Fin 3) ℂ
def colorRepresentation := ((defining 3).tprod (defining 3)).tprod (defining 3)

def colorPairing : IntertwiningMap colorRepresentation (Representation.trivial ℂ ColorGroup ℂ) where
  toLinearMap := colorTensor
  isIntertwining' g := by
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext; intro a
    apply LinearMap.ext; intro b
    apply LinearMap.ext; intro c
    exact eps3_invariant g.val (Matrix.mem_specialUnitaryGroup_iff.mp g.property).2 a b c

def colorProbe := (colorBasis 0 ⊗ₜ[ℂ] colorBasis 1) ⊗ₜ[ℂ] colorBasis 2

theorem color_normalized : colorPairing colorProbe = 1 := by
  norm_num [colorPairing, colorProbe, colorTensor_tmul, eps3, colorBasis, Fin.ext_iff]

theorem color_unique (f : IntertwiningMap colorRepresentation (Representation.trivial ℂ ColorGroup ℂ)) :
    f = f colorProbe • colorPairing := by
  let c := TensorProduct.curry (TensorProduct.curry f.toLinearMap)
  have hc : ∀ g a b d, c (defining 3 g a) (defining 3 g b) (defining 3 g d) = c a b d := by
    intro g a b d
    exact IntertwiningMap.isIntertwining _ _ f g ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] d)
  have he := SMEpsilonUniqueness.color_unique c hc
  apply IntertwiningMap.ext
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply LinearMap.ext; intro a
  apply LinearMap.ext; intro b
  apply LinearMap.ext; intro d
  exact congrArg (fun k => k a b d) he

abbrev LocalGroup := ColorGroup × (FourDoubletInvariant.Group × WeylSpinor.Group)
def representation := external colorRepresentation FourWeakWeylCompleteness.representation
abbrev Coefficient := IntertwiningMap representation (Representation.trivial ℂ LocalGroup ℂ)
def pairing (ij : Fin 2 × Fin 2) := coefficient colorPairing (FourWeakWeylCompleteness.pairing ij)
def probe (ij : Fin 2 × Fin 2) := colorProbe ⊗ₜ[ℂ] FourWeakWeylCompleteness.probe ij

theorem pairing_probe (ij kl : Fin 2 × Fin 2) :
    pairing ij (probe kl) = if ij = kl then 1 else 0 := by
  change colorPairing colorProbe * FourWeakWeylCompleteness.pairing ij
    (FourWeakWeylCompleteness.probe kl) = _
  rw [color_normalized, one_mul, FourWeakWeylCompleteness.pairing_probe]

theorem reconstruction (f : Coefficient) : f = ∑ ij, f (probe ij) • pairing ij :=
  FiniteInvariantFactor.product_left_line _ _ _ _ color_unique _ _
    FourWeakWeylCompleteness.reconstruction f

variable {R Q L : Type*} [Group R] [AddCommGroup Q] [Module ℂ Q]
  [AddCommGroup L] [Module ℂ L]
  (q : Representation ℂ R Q) (l : Representation ℂ R L)

def flavor := (q.tprod q).tprod (q.tprod l)

/-- Four residual coordinates before imposing the identical-quark exchanges. -/
def homEquiv :
    IntertwiningMap (external representation (flavor q l))
      (Representation.trivial ℂ (LocalGroup × R) ℂ) ≃ₗ[ℂ]
    (Fin 2 × Fin 2 → IntertwiningMap (flavor q l) (Representation.trivial ℂ R ℂ)) :=
  FiniteInvariantFactor.equiv _ _ pairing probe pairing_probe reconstruction

end
end Physics.QqqlLocalCompleteness
