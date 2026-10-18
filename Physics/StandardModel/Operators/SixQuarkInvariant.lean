import Physics.StandardModel.Gauge.SixColorInvariant
import Physics.FieldTheory.Spinor.SixWeylMultilinear
import Physics.StandardModel.Operators.DeltaBTwoSixQuark
import Math.RepresentationTheory.SixSlotRestrictionLift
import Mathlib.LinearAlgebra.TensorProduct.Basis

open Math

/-!
# Separating color and Weyl invariance on six quark slots

The domain is the actual tensor product `Color ⊗ Spin`, not the set of
decomposable inputs. Color reconstruction is applied with spins fixed. Its
five coordinate functions are multilinear, invariant Weyl coefficients.
Weyl spanning then gives twenty-five products. Tensor-product basis
extensionality transports the pure-input formula to the entire domain.
No species alternation or two-dimensional conclusion is assumed here.
-/
namespace GUT.SixQuarkInvariant

set_option autoImplicit false
noncomputable section
open SMEpsilonTensor
open scoped TensorProduct

abbrev Spin := WeylSpinor.Space
abbrev Quark := Color ⊗[ℂ] Spin
abbrev Coefficient := MultilinearMap ℂ (fun _ : Fin 6 => Quark) ℂ

def colorAction (g : SixColorInvariant.Group) : Quark →ₗ[ℂ] Quark :=
  TensorProduct.map (Math.SmallSpecialUnitary.defining 3 g) LinearMap.id

def spinAction (g : WeylSpinor.Group) : Quark →ₗ[ℂ] Quark :=
  TensorProduct.map LinearMap.id (WeylSpinor.right g)

/-- Independent color and right-Weyl invariance, without a contraction ansatz. -/
def IsInvariant (f : Coefficient) : Prop :=
  (∀ g v, f (fun i => colorAction g (v i)) = f v) ∧
  (∀ g v, f (fun i => spinAction g (v i)) = f v)

def fixedSpin (f : Coefficient) (s : Fin 6 → Spin) : SixColorInvariant.Coefficient :=
  f.compLinearMap (fun i => (TensorProduct.mk ℂ Color Spin).flip (s i))

def fixedColor (f : Coefficient) (v : Fin 6 → Color) : SixWeylMultilinear.Coefficient :=
  f.compLinearMap (fun i => TensorProduct.mk ℂ Color Spin (v i))

@[simp] theorem fixedSpin_apply (f : Coefficient) (s : Fin 6 → Spin)
    (v : Fin 6 → Color) : fixedSpin f s v = f (fun i => v i ⊗ₜ[ℂ] s i) := rfl

@[simp] theorem fixedColor_apply (f : Coefficient) (v : Fin 6 → Color)
    (s : Fin 6 → Spin) : fixedColor f v s = f (fun i => v i ⊗ₜ[ℂ] s i) := rfl

theorem fixedSpin_invariant (f : Coefficient) (hf : IsInvariant f) (s : Fin 6 → Spin) :
    SixColorInvariant.IsInvariant (fixedSpin f s) := by
  intro g v
  simpa [colorAction] using hf.1 g (fun i => v i ⊗ₜ[ℂ] s i)

theorem fixedColor_invariant (f : Coefficient) (hf : IsInvariant f)
    (v : Fin 6 → Color) : SixWeylMultilinear.IsInvariant (fixedColor f v) := by
  intro g s
  simpa [spinAction] using hf.2 g (fun i => v i ⊗ₜ[ℂ] s i)

def colorProbe (r : Fin 15) : Fin 6 → Color :=
  fun i => colorBasis (SixColorInvariant.representative r i)

/-- Color coordinates remain multilinear maps in the six spin variables. -/
def spinCoordinates (f : Coefficient) : Fin 5 → SixWeylMultilinear.Coefficient := ![
  fixedColor f (colorProbe 9) - fixedColor f (colorProbe 0),
  fixedColor f (colorProbe 4), fixedColor f (colorProbe 3),
  fixedColor f (colorProbe 1), fixedColor f (colorProbe 0)]

theorem spinCoordinates_apply (f : Coefficient) (p : Fin 5) (s : Fin 6 → Spin) :
    spinCoordinates f p s = SixColorInvariant.coordinates (fixedSpin f s) p := by
  fin_cases p <;> simp [spinCoordinates, SixColorInvariant.coordinates,
    SixColorInvariant.basisValue, colorProbe]

theorem spinCoordinates_invariant (f : Coefficient) (hf : IsInvariant f) (p : Fin 5) :
    SixWeylMultilinear.IsInvariant (spinCoordinates f p) := by
  intro g s
  have hi (v : Fin 6 → Color) := fixedColor_invariant f hf v g s
  fin_cases p <;> simp [spinCoordinates, -fixedColor_apply, hi]

/-- A separate basis argument ensures that decomposable slots determine the
coefficient even though arbitrary quarks need not be decomposable. -/
theorem pure_ext {f h : Coefficient}
    (he : ∀ (v : Fin 6 → Color) (s : Fin 6 → Spin),
      f (fun i => v i ⊗ₜ[ℂ] s i) = h (fun i => v i ⊗ₜ[ℂ] s i)) : f = h := by
  let b := (Pi.basisFun ℂ (Fin 3)).tensorProduct (Pi.basisFun ℂ (Fin 2))
  apply Module.Basis.ext_multilinear (fun _ => b)
  intro idx
  simpa [b, Module.Basis.tensorProduct_apply', Pi.basisFun_apply,
    colorBasis, weakBasis] using
    he (fun i => colorBasis (idx i).1) (fun i => weakBasis (idx i).2)

/-- Arbitrary invariant six-quark coefficients have a 5-by-5 contraction
expansion on every decomposable input, with coefficients independent of input.
Together with `pure_ext`, this is a spanning statement on the full domain. -/
theorem exists_product_coordinates (f : Coefficient) (hf : IsInvariant f) :
    ∃ c : Fin 5 → Fin 5 → ℂ, ∀ (v : Fin 6 → Color) (s : Fin 6 → Spin),
      f (fun i => v i ⊗ₜ[ℂ] s i) = ∑ p, ∑ q,
        c p q * SixColorInvariant.pairingValue p v *
          SixWeylMultilinear.pairingValue q s := by
  classical
  have hs (p : Fin 5) := SixWeylMultilinear.exists_pairing_coordinates
    (spinCoordinates f p) (spinCoordinates_invariant f hf p)
  choose c hc using hs
  refine ⟨c, ?_⟩
  intro v s
  have he := congrArg (fun h : SixColorInvariant.Coefficient => h v)
    (SixColorInvariant.reconstruct_coordinates (fixedSpin f s)
      (fixedSpin_invariant f hf s)).symm
  simp only [fixedSpin_apply, SixColorInvariant.reconstruct_apply] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← spinCoordinates_apply, hc p]
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul,
    SixWeylMultilinear.pairing_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  ring

def coordinates (f : Coefficient) : Fin 5 → Fin 5 → ℂ :=
  fun p => SixWeylMultilinear.coordinates (spinCoordinates f p)

/-- The product coordinates are actual probes of the coefficient, not
input-dependent choices of decomposition. -/
theorem coordinates_formula (f : Coefficient) (hf : IsInvariant f)
    (v : Fin 6 → Color) (s : Fin 6 → Spin) :
    f (fun i => v i ⊗ₜ[ℂ] s i) = ∑ p, ∑ q,
      coordinates f p q * SixColorInvariant.pairingValue p v *
        SixWeylMultilinear.pairingValue q s := by
  have he := congrArg (fun h : SixColorInvariant.Coefficient => h v)
    (SixColorInvariant.reconstruct_coordinates (fixedSpin f s)
      (fixedSpin_invariant f hf s)).symm
  simp only [fixedSpin_apply, SixColorInvariant.reconstruct_apply] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← spinCoordinates_apply,
    ← SixWeylMultilinear.reconstruct_coordinates (spinCoordinates f p)
      (spinCoordinates_invariant f hf p)]
  simp only [SixWeylMultilinear.reconstruct, _root_.sum_apply,
    _root_.smul_apply, smul_eq_mul, SixWeylMultilinear.pairing_apply,
    Finset.sum_mul, coordinates]
  apply Finset.sum_congr rfl
  intro q hq
  ring

theorem eq_of_coordinates {f h : Coefficient} (hf : IsInvariant f)
    (hh : IsInvariant h) (hc : coordinates f = coordinates h) : f = h := by
  apply pure_ext
  intro v s
  rw [coordinates_formula f hf, coordinates_formula h hh, hc]

/-- Project a quark onto its color component at one spin-basis index. -/
def colorComponent (j : Fin 2) : Quark →ₗ[ℂ] Color :=
  (TensorProduct.rid ℂ Color).toLinearMap.comp
    (TensorProduct.map LinearMap.id (LinearMap.proj j))

@[simp] theorem colorComponent_tmul (j : Fin 2) (v : Color) (s : Spin) :
    colorComponent j (v ⊗ₜ[ℂ] s) = s j • v := by simp [colorComponent]

/-- Bilinear tensor extension of two six-linear scalar coefficients. Only
the 64 spin-basis choices are summed, not all quark basis coordinates. -/
def combine (C : SixColorInvariant.Coefficient) (W : SixWeylMultilinear.Coefficient) :
    Coefficient := ∑ idx : Fin 6 → Fin 2,
      W (fun i => weakBasis (idx i)) •
        C.compLinearMap (fun i => colorComponent (idx i))

theorem combine_apply (C : SixColorInvariant.Coefficient)
    (W : SixWeylMultilinear.Coefficient) (v : Fin 6 → Color) (s : Fin 6 → Spin) :
    combine C W (fun i => v i ⊗ₜ[ℂ] s i) = C v * W s := by
  have hs (x : Spin) : (∑ j : Fin 2, x j • weakBasis j) = x := by
    ext j; fin_cases j <;> simp [Fin.sum_univ_two, weakBasis]
  have he := W.map_sum (fun i j => s i j • weakBasis j)
  simp only [hs] at he
  simp_rw [W.map_smul_univ, smul_eq_mul] at he
  simp only [combine, _root_.sum_apply, _root_.smul_apply,
    MultilinearMap.compLinearMap_apply, colorComponent_tmul, C.map_smul_univ,
    smul_eq_mul]
  calc
    _ = C v * ∑ idx : Fin 6 → Fin 2,
        (∏ i, s i (idx i)) * W (fun i => weakBasis (idx i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro idx hi
      ring
    _ = _ := by rw [← he]

def productPairing (p q : Fin 5) : Coefficient :=
  combine (SixColorInvariant.pairing p) (SixWeylMultilinear.pairing q)

@[simp] theorem productPairing_apply (p q : Fin 5)
    (v : Fin 6 → Color) (s : Fin 6 → Spin) :
    productPairing p q (fun i => v i ⊗ₜ[ℂ] s i) =
      SixColorInvariant.pairingValue p v * SixWeylMultilinear.pairingValue q s :=
  combine_apply _ _ _ _

theorem productPairing_invariant (p q : Fin 5) : IsInvariant (productPairing p q) := by
  constructor
  · intro g
    have he : (productPairing p q).compLinearMap (fun _ => colorAction g) =
        productPairing p q := by
      apply pure_ext
      intro v s
      simpa [colorAction] using
        congrArg (fun z => z * SixWeylMultilinear.pairing q s)
          (SixColorInvariant.pairing_invariant p g v)
    intro v
    exact congrArg (fun F : Coefficient => F v) he
  · intro g
    have he : (productPairing p q).compLinearMap (fun _ => spinAction g) =
        productPairing p q := by
      apply pure_ext
      intro v s
      simpa [spinAction] using
        congrArg (fun z => SixColorInvariant.pairing p v * z)
          (SixWeylMultilinear.pairing_invariant q g s)
    intro v
    exact congrArg (fun F : Coefficient => F v) he

def reconstruct (c : Fin 5 → Fin 5 → ℂ) : Coefficient :=
  ∑ p, ∑ q, c p q • productPairing p q

@[simp] theorem reconstruct_apply (c : Fin 5 → Fin 5 → ℂ)
    (v : Fin 6 → Color) (s : Fin 6 → Spin) :
    reconstruct c (fun i => v i ⊗ₜ[ℂ] s i) = ∑ p, ∑ q,
      c p q * SixColorInvariant.pairingValue p v *
        SixWeylMultilinear.pairingValue q s := by
  simp [reconstruct, smul_eq_mul, mul_assoc]

theorem reconstruct_invariant (c : Fin 5 → Fin 5 → ℂ) :
    IsInvariant (reconstruct c) := by
  constructor <;> intro g v <;> simp only [reconstruct, _root_.sum_apply,
    _root_.smul_apply]
  · simp only [(productPairing_invariant _ _).1]
  · simp only [(productPairing_invariant _ _).2]

theorem reconstruct_coordinates (f : Coefficient) (hf : IsInvariant f) :
    reconstruct (coordinates f) = f := by
  apply pure_ext
  intro v s
  exact (reconstruct_apply _ v s).trans (coordinates_formula f hf v s).symm

/-- The 25 product coordinates are unique on the full quark-slot domain. -/
theorem product_coordinates_unique (f : Coefficient) (c : Fin 5 → Fin 5 → ℂ)
    (hc : ∀ (v : Fin 6 → Color) (s : Fin 6 → Spin),
      f (fun i => v i ⊗ₜ[ℂ] s i) = ∑ p, ∑ q,
        c p q * SixColorInvariant.pairingValue p v *
          SixWeylMultilinear.pairingValue q s) : c = coordinates f := by
  have hcolor (s : Fin 6 → Spin) :
      SixColorInvariant.reconstruct
        (fun p => ∑ q, c p q * SixWeylMultilinear.pairingValue q s) =
          fixedSpin f s := by
    ext v
    rw [SixColorInvariant.reconstruct_apply, fixedSpin_apply, hc]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  have hspin (p : Fin 5) : SixWeylMultilinear.reconstruct (c p) =
      spinCoordinates f p := by
    ext s
    have he := congrFun (congrArg SixColorInvariant.coordinates (hcolor s)) p
    rw [SixColorInvariant.coordinates_reconstruct] at he
    simpa [SixWeylMultilinear.reconstruct, spinCoordinates_apply] using he
  ext p q
  have he := congrArg SixWeylMultilinear.coordinates (hspin p)
  rw [SixWeylMultilinear.coordinates_reconstruct] at he
  exact congrFun he q

theorem coordinates_reconstruct (c : Fin 5 → Fin 5 → ℂ) :
    coordinates (reconstruct c) = c :=
  (product_coordinates_unique _ c (reconstruct_apply c)).symm

/-- Read the interleaved six quark slots of an ordered linear functional. -/
def orderedCoefficient (f : SixSlotAlternation.OrderedSpace Quark Quark →ₗ[ℂ] ℂ) :
    Coefficient :=
  (SixSlotAlternation.ordered f).compLinearMap
    (fun _ => LinearMap.prod LinearMap.id LinearMap.id)

/-- Only within-species permutations carry a statistics condition on the
ordered restriction. Swapping an up and a down slot is not included. -/
def IsSpeciesAlternating (f : Coefficient) : Prop :=
  ∀ (p : Equiv.Perm (Fin 6)), SixSlotAlternation.PreservesPattern p →
    ∀ v, f (v ∘ p) = Equiv.Perm.sign p • f v

@[simp] theorem orderedCoefficient_apply
    (f : SixSlotAlternation.OrderedSpace Quark Quark →ₗ[ℂ] ℂ)
    (v : Fin 6 → Quark) :
    orderedCoefficient f v = f (((v 0 ⊗ₜ[ℂ] v 1) ⊗ₜ[ℂ]
      (v 2 ⊗ₜ[ℂ] v 3)) ⊗ₜ[ℂ] (v 4 ⊗ₜ[ℂ] v 5)) := rfl

private theorem ordered_action
    (f : Representation.IntertwiningMap
      (SixSlotAlternation.orderedRepresentation DeltaBTwoSixQuark.upField
        DeltaBTwoSixQuark.downField)
      (Representation.trivial ℂ DeltaBTwoSixQuark.SymmetryGroup ℂ))
    (g : DeltaBTwoSixQuark.SymmetryGroup) (L : Quark →ₗ[ℂ] Quark)
    (hu : DeltaBTwoSixQuark.upField g = L)
    (hd : DeltaBTwoSixQuark.downField g = L) (v : Fin 6 → Quark) :
    orderedCoefficient f.toLinearMap (fun i => L (v i)) =
      orderedCoefficient f.toLinearMap v := by
  have hi := Representation.IntertwiningMap.isIntertwining _ _ f g
    (((v 0 ⊗ₜ[ℂ] v 1) ⊗ₜ[ℂ] (v 2 ⊗ₜ[ℂ] v 3)) ⊗ₜ[ℂ]
      (v 4 ⊗ₜ[ℂ] v 5))
  simpa [orderedCoefficient_apply, SixSlotAlternation.orderedRepresentation,
    Representation.tprod_apply, hu, hd] using hi

/-- Physical ordered gauge/Lorentz intertwiners satisfy the independent
invariance hypotheses used above; no new invariance assumption is imposed. -/
theorem orderedCoefficient_invariant
    (f : Representation.IntertwiningMap
      (SixSlotAlternation.orderedRepresentation DeltaBTwoSixQuark.upField
        DeltaBTwoSixQuark.downField)
      (Representation.trivial ℂ DeltaBTwoSixQuark.SymmetryGroup ℂ)) :
    IsInvariant (orderedCoefficient f.toLinearMap) := by
  have hc (g : SixColorInvariant.Group) :
      DeltaBTwoSixQuark.upField ((g, 1, 1), 1) = colorAction g ∧
      DeltaBTwoSixQuark.downField ((g, 1, 1), 1) = colorAction g := by
    constructor <;> apply TensorProduct.ext <;> ext a s <;>
      simp [DeltaBTwoSixQuark.upField, DeltaBTwoSixQuark.downField,
        ExternalInvariantTensor.external, StandardSMGaugeTensor.upRight,
        StandardSMGaugeTensor.downRight, StandardSMGaugeTensor.twist,
        StandardSMGaugeTensor.phase, StandardSMGaugeTensor.color,
        colorAction, Math.SmallSpecialUnitary.defining]
  have hs (g : WeylSpinor.Group) :
      DeltaBTwoSixQuark.upField (1, g) = spinAction g ∧
      DeltaBTwoSixQuark.downField (1, g) = spinAction g := by
    constructor <;> apply TensorProduct.ext <;> ext a s <;>
      simp [DeltaBTwoSixQuark.upField, DeltaBTwoSixQuark.downField,
        ExternalInvariantTensor.external, spinAction]
  exact ⟨fun g v => ordered_action f ((g, 1, 1), 1) (colorAction g)
    (hc g).1 (hc g).2 v,
    fun g v => ordered_action f (1, g) (spinAction g) (hs g).1 (hs g).2 v⟩

/-- Apply the decomposition directly to the intrinsic exterior coefficient,
via its already-proved restriction. This does not require the degree premise;
that premise is needed for the reverse exterior reconstruction. -/
theorem exteriorRestriction_product_coordinates
    (f : SixSlotSpeciesDegree.coefficients DeltaBTwoSixQuark.upField
      DeltaBTwoSixQuark.downField) :
    ∃ c : Fin 5 → Fin 5 → ℂ, ∀ (v : Fin 6 → Color) (s : Fin 6 → Spin),
      orderedCoefficient (SixSlotRestrictionLift.restriction
        DeltaBTwoSixQuark.upField DeltaBTwoSixQuark.downField f).toLinearMap
        (fun i => v i ⊗ₜ[ℂ] s i) = ∑ p, ∑ q,
        c p q * SixColorInvariant.pairingValue p v *
          SixWeylMultilinear.pairingValue q s :=
  exists_product_coordinates _ (orderedCoefficient_invariant _)

def exteriorRestriction
    (f : SixSlotSpeciesDegree.coefficients DeltaBTwoSixQuark.upField
      DeltaBTwoSixQuark.downField) : Coefficient :=
  orderedCoefficient (SixSlotRestrictionLift.restriction
    DeltaBTwoSixQuark.upField DeltaBTwoSixQuark.downField f).toLinearMap

private def speciesSlots (v : Fin 6 → Quark) :
    Fin 6 → SixSlotAlternation.Fields Quark Quark :=
  fun i => if i = 0 ∨ i = 2 then (v i, 0) else (0, v i)

theorem exteriorRestriction_apply
    (f : SixSlotSpeciesDegree.coefficients DeltaBTwoSixQuark.upField
      DeltaBTwoSixQuark.downField) (v : Fin 6 → Quark) :
    exteriorRestriction f v = f (exteriorPower.ιMulti ℂ 6
      (SixSlotAlternation.slots (v 0) (v 2) (v 1) (v 3) (v 4) (v 5))) := by
  exact SixSlotRestrictionLift.linearRestriction_apply _ _ f _ _ _ _ _ _

private theorem speciesSlots_eq (v : Fin 6 → Quark) :
    speciesSlots v = SixSlotAlternation.slots
      (v 0) (v 2) (v 1) (v 3) (v 4) (v 5) := by
  ext i <;> fin_cases i <;> simp [speciesSlots, SixSlotAlternation.slots]

private theorem pattern_membership :
    ∀ p : Equiv.Perm (Fin 6), SixSlotAlternation.PreservesPattern p →
      ∀ i, (p i = 0 ∨ p i = 2) ↔ (i = 0 ∨ i = 2) := by
  decide +kernel

theorem exteriorRestriction_speciesAlternating
    (f : SixSlotSpeciesDegree.coefficients DeltaBTwoSixQuark.upField
      DeltaBTwoSixQuark.downField) : IsSpeciesAlternating (exteriorRestriction f) := by
  intro p hp v
  have he (v : Fin 6 → Quark) : exteriorRestriction f v =
      SixSlotSpeciesRestriction.evaluation DeltaBTwoSixQuark.upField
        DeltaBTwoSixQuark.downField f (speciesSlots v) := by
    rw [exteriorRestriction_apply, speciesSlots_eq]
    rfl
  rw [he, he]
  have hv : speciesSlots (v ∘ p) = speciesSlots v ∘ p := by
    ext i <;> simp [speciesSlots, pattern_membership p hp i]
  rw [hv]
  exact (SixSlotSpeciesRestriction.evaluation _ _ f).map_perm _ p

/-- Species statistics becomes explicit linear constraints on the 25
coordinates. This lemma is a constraint, not a claim that its kernel has
already been shown to be two-dimensional. -/
theorem species_coordinate_constraint (f : Coefficient) (hf : IsInvariant f)
    (ha : IsSpeciesAlternating f) (p : Equiv.Perm (Fin 6))
    (hp : SixSlotAlternation.PreservesPattern p)
    (v : Fin 6 → Color) (s : Fin 6 → Spin) :
    (∑ a, ∑ b, coordinates f a b * SixColorInvariant.pairingValue a (v ∘ p) *
        SixWeylMultilinear.pairingValue b (s ∘ p)) =
      Equiv.Perm.sign p • (∑ a, ∑ b, coordinates f a b *
        SixColorInvariant.pairingValue a v * SixWeylMultilinear.pairingValue b s) := by
  rw [← coordinates_formula f hf, ← coordinates_formula f hf]
  exact ha p hp (fun i => v i ⊗ₜ[ℂ] s i)

/-- The 25 coordinates already separate intrinsic degree-(2,4) coefficients.
The final two-coordinate quotient must refine this injection, not redefine
the intrinsic sector to be a contraction-generated image. -/
theorem exterior_eq_of_coordinates
    (f h : SixSlotSpeciesDegree.coefficients DeltaBTwoSixQuark.upField
      DeltaBTwoSixQuark.downField)
    (hf : SixSlotSpeciesDegree.HasDegree DeltaBTwoSixQuark.upField
      DeltaBTwoSixQuark.downField f)
    (hh : SixSlotSpeciesDegree.HasDegree DeltaBTwoSixQuark.upField
      DeltaBTwoSixQuark.downField h)
    (hc : coordinates (exteriorRestriction f) = coordinates (exteriorRestriction h)) :
    f = h := by
  have he : exteriorRestriction f = exteriorRestriction h :=
    eq_of_coordinates (orderedCoefficient_invariant _) (orderedCoefficient_invariant _) hc
  apply SixSlotSpeciesRestriction.slots_ext _ _ f h hf hh
  intro u₁ u₂ d₁ d₂ d₃ d₄
  have hv := congrArg (fun F : Coefficient => F ![u₁,d₁,u₂,d₂,d₃,d₄]) he
  simpa [exteriorRestriction_apply] using hv

end
end GUT.SixQuarkInvariant
