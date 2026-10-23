import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkTwoCoordinates
import Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoContractionRelations.Basic

open Math

/-! Conventional ordered contractions on the actual quark tensor domain.
The exterior descent here is unnormalized, as in the existence pilot. -/
namespace Physics.SixQuarkConventionalBasis
set_option autoImplicit false
noncomputable section
open SMEpsilonTensor SixQuarkInvariant SixQuarkTwoCoordinates
open scoped TensorProduct

def colorSSS : SixColorInvariant.Coefficient :=
  MultilinearMap.mk'
    (fun v => DeltaBTwoContractionRelations.colorSSS
      (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))
    (by intro v i x y; fin_cases i <;>
      simp [DeltaBTwoContractionRelations.colorSSS, Function.update, eps3,
        add_mul, mul_add] <;> ring)
    (by intro v i z x; fin_cases i <;>
      simp [DeltaBTwoContractionRelations.colorSSS, Function.update, eps3,
        smul_eq_mul] <;> ring)

def colorAAS : SixColorInvariant.Coefficient := DeltaBTwoSixQuark.colorAASMulti

theorem colorSSS_invariant : SixColorInvariant.IsInvariant colorSSS := by
  intro g v
  have hd := (Matrix.mem_specialUnitaryGroup_iff.mp g.property).2
  have he (a b c : Color) : eps3 (SmallSpecialUnitary.defining 3 g a)
      (SmallSpecialUnitary.defining 3 g b) (SmallSpecialUnitary.defining 3 g c) =
        eps3 a b c := by
    simpa [SmallSpecialUnitary.defining, Matrix.toLin'_apply] using
      eps3_invariant _ hd a b c
  simp only [colorSSS, MultilinearMap.mk'_apply,
    DeltaBTwoContractionRelations.colorSSS, he]

theorem colorAAS_invariant : SixColorInvariant.IsInvariant colorAAS := by
  intro g v
  have hd := (Matrix.mem_specialUnitaryGroup_iff.mp g.property).2
  have he (a b c : Color) : eps3 (SmallSpecialUnitary.defining 3 g a)
      (SmallSpecialUnitary.defining 3 g b) (SmallSpecialUnitary.defining 3 g c) =
        eps3 a b c := by
    simpa [SmallSpecialUnitary.defining, Matrix.toLin'_apply] using
      eps3_invariant _ hd a b c
  simp only [colorAAS, DeltaBTwoSixQuark.colorAASMulti,
    MultilinearMap.mk'_apply, he]

theorem combine_invariant (C : SixColorInvariant.Coefficient)
    (W : SixWeylMultilinear.Coefficient) (hC : SixColorInvariant.IsInvariant C)
    (hW : SixWeylMultilinear.IsInvariant W) : IsInvariant (combine C W) := by
  constructor
  · intro g v
    have he : (combine C W).compLinearMap (fun _ => colorAction g) = combine C W := by
      apply pure_ext
      intro a s
      simp [colorAction, combine_apply, hC g a]
    exact congrArg (fun F : Coefficient => F v) he
  · intro g v
    have he : (combine C W).compLinearMap (fun _ => spinAction g) = combine C W := by
      apply pure_ext
      intro a s
      simp [spinAction, combine_apply, hW g s]
    exact congrArg (fun F : Coefficient => F v) he

def orderedO2 : Coefficient := combine colorSSS (SixWeylMultilinear.pairing 0)
def orderedO3 : Coefficient := combine colorAAS (SixWeylMultilinear.pairing 0)
def orderedO1 : Coefficient := -(orderedO2.domDomCongr (Equiv.swap 1 2))

theorem orderedO2_apply (v : Fin 6 → Color) (s : Fin 6 → Spin) :
    orderedO2 (fun i => v i ⊗ₜ[ℂ] s i) =
      DeltaBTwoContractionRelations.orderedO2Value
        (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)
        (s 0) (s 1) (s 2) (s 3) (s 4) (s 5) := by
  simp [orderedO2, combine_apply, colorSSS, SixWeylMultilinear.pairingValue,
    SixWeylInvariant.pairingValue, DeltaBTwoContractionRelations.orderedO2Value,
    mul_assoc]

theorem orderedO3_apply (v : Fin 6 → Color) (s : Fin 6 → Spin) :
    orderedO3 (fun i => v i ⊗ₜ[ℂ] s i) =
      DeltaBTwoContractionRelations.orderedO3Value
        (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)
        (s 0) (s 1) (s 2) (s 3) (s 4) (s 5) := by
  simp [orderedO3, combine_apply, colorAAS, DeltaBTwoSixQuark.colorAASMulti,
    SixWeylMultilinear.pairingValue, SixWeylInvariant.pairingValue,
    DeltaBTwoContractionRelations.orderedO3Value,
    DeltaBTwoContractionRelations.colorAAS, mul_assoc]

theorem orderedO1_apply (v : Fin 6 → Color) (s : Fin 6 → Spin) :
    orderedO1 (fun i => v i ⊗ₜ[ℂ] s i) =
      DeltaBTwoContractionRelations.orderedO1Value
        (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)
        (s 0) (s 1) (s 2) (s 3) (s 4) (s 5) := by
  change -orderedO2 (fun i => v (Equiv.swap 1 2 i) ⊗ₜ[ℂ]
    s (Equiv.swap 1 2 i)) = _
  rw [orderedO2_apply]
  simp [Equiv.swap_apply_def, DeltaBTwoContractionRelations.orderedO2Value,
    DeltaBTwoContractionRelations.orderedO1Value]

theorem orderedO2_invariant : IsInvariant orderedO2 :=
  combine_invariant _ _ colorSSS_invariant (SixWeylMultilinear.pairing_invariant 0)

theorem orderedO3_invariant : IsInvariant orderedO3 :=
  combine_invariant _ _ colorAAS_invariant (SixWeylMultilinear.pairing_invariant 0)

attribute [local irreducible] orderedO2

theorem orderedO1_invariant : IsInvariant orderedO1 := by
  constructor <;> intro g v
  · simpa only [orderedO1, _root_.neg_apply, MultilinearMap.domDomCongr_apply,
      Function.comp_def] using
      congrArg (fun z : ℂ => -z) (orderedO2_invariant.1 g (v ∘ Equiv.swap 1 2))
  · simpa only [orderedO1, _root_.neg_apply, MultilinearMap.domDomCongr_apply,
      Function.comp_def] using
      congrArg (fun z : ℂ => -z) (orderedO2_invariant.2 g (v ∘ Equiv.swap 1 2))

/-- Unnormalized exterior descent of any ordered invariant. -/
def descend (f : Coefficient) (hf : IsInvariant f) : Sector :=
  ⟨SixSlotAlternation.coefficient DeltaBTwoSixQuark.upField
    DeltaBTwoSixQuark.downField (orderedIntertwiner f hf),
    SixSlotSpeciesDegree.coefficient_hasDegree _ _ _⟩

def O1 : Sector := descend orderedO1 orderedO1_invariant
def O2 : Sector := descend orderedO2 orderedO2_invariant
def O3 : Sector := descend orderedO3 orderedO3_invariant

attribute [local irreducible] orderedO3 orderedLift DeltaBTwoSixQuark.orderedContraction

theorem orderedO3_eq_existing : orderedLift orderedO3 =
    DeltaBTwoSixQuark.orderedContraction := by
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply LinearMap.ext; intro a
  apply LinearMap.ext; intro s
  apply TensorProduct.ext
  apply LinearMap.ext; intro b
  apply LinearMap.ext; intro t
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply LinearMap.ext; intro c
  apply LinearMap.ext; intro u
  apply TensorProduct.ext
  apply LinearMap.ext; intro d
  apply LinearMap.ext; intro v
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply LinearMap.ext; intro e
  apply LinearMap.ext; intro w
  apply TensorProduct.ext
  apply LinearMap.ext; intro f
  apply LinearMap.ext; intro x
  change orderedLift orderedO3 ((((a ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] t)) ⊗ₜ[ℂ]
    ((c ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] (d ⊗ₜ[ℂ] v))) ⊗ₜ[ℂ]
    ((e ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] (f ⊗ₜ[ℂ] x))) =
    DeltaBTwoSixQuark.orderedContraction ((((a ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] t)) ⊗ₜ[ℂ]
    ((c ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] (d ⊗ₜ[ℂ] v))) ⊗ₜ[ℂ]
    ((e ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] (f ⊗ₜ[ℂ] x)))
  rw [orderedLift_apply]
  have hvec : ![a ⊗ₜ[ℂ] s, b ⊗ₜ[ℂ] t, c ⊗ₜ[ℂ] u, d ⊗ₜ[ℂ] v,
      e ⊗ₜ[ℂ] w, f ⊗ₜ[ℂ] x] =
      (fun i => (![a,b,c,d,e,f] i) ⊗ₜ[ℂ] (![s,t,u,v,w,x] i)) := by
    ext i; fin_cases i <;> rfl
  rw [hvec]
  rw [orderedO3_apply]
  simp [DeltaBTwoContractionRelations.orderedO3Value,
    DeltaBTwoContractionRelations.colorAAS]

theorem O3_eq_existing : O3.1 = DeltaBTwoSixQuark.exteriorCoefficient := by
  have he : orderedIntertwiner orderedO3 orderedO3_invariant =
      DeltaBTwoSixQuark.orderedIntertwiner := by
    apply Representation.IntertwiningMap.ext
    exact orderedO3_eq_existing
  change SixSlotAlternation.coefficient _ _ _ = _
  rw [he]
  rfl

theorem O3_witness : O3.1 (exteriorPower.ιMulti ℂ 6 DeltaBTwoSixQuark.witness) = 24 := by
  rw [O3_eq_existing]
  exact DeltaBTwoSixQuark.exteriorCoefficient_witness

end
end Physics.SixQuarkConventionalBasis
