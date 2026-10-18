import Physics.StandardModel.Operators.SixQuarkSpeciesQuotient
import Math.LinearAlgebra.StatisticalCompleteness
import Math.RepresentationTheory.IndexedTensorSeparation
import Mathlib.LinearAlgebra.Basis.VectorSpace

open Math

/-! Gauge/Weyl coordinates with arbitrary slot multiplicities. Flavor arguments
are retained when a species transposition acts; they are not scalar constants. -/
namespace GUT.SixQuarkFlavorCoordinates
set_option autoImplicit false
noncomputable section
open SixQuarkInvariant SixQuarkSpeciesQuotient
open scoped TensorProduct
attribute [local irreducible] reconstruct

/-- Coordinate extraction is linear in the gauge/Weyl coefficient. -/
def coordinateLinear : Coefficient →ₗ[ℂ] (Fin 5 → Fin 5 → ℂ) where
  toFun := coordinates
  map_add' f h := by
    ext p q
    fin_cases p <;> fin_cases q <;>
      simp [coordinates, spinCoordinates, SixWeylMultilinear.coordinates,
        SixWeylMultilinear.basisValue, fixedColor] <;> ring
  map_smul' z f := by
    ext p q
    fin_cases p <;> fin_cases q <;>
      simp [coordinates, spinCoordinates, SixWeylMultilinear.coordinates,
        SixWeylMultilinear.basisValue, fixedColor, smul_eq_mul] <;> ring

def reconstructLinear : (Fin 5 → Fin 5 → ℂ) →ₗ[ℂ] Coefficient where
  toFun := reconstruct
  map_add' c d := by
    simp [reconstruct, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' z c := by
    simp [reconstruct, Pi.smul_apply, Finset.smul_sum, smul_smul]

section Dependent
variable {V : Fin 6 → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

abbrev FlavorCoefficient := MultilinearMap ℂ (fun i => Quark ⊗[ℂ] V i) ℂ

def fixedFlavor (f : FlavorCoefficient (V := V)) (t : ∀ i, V i) : Coefficient :=
  f.compLinearMap (fun i => (TensorProduct.mk ℂ Quark (V i)).flip (t i))

@[simp] theorem fixedFlavor_apply (f : FlavorCoefficient (V := V))
    (t : ∀ i, V i) (q : Fin 6 → Quark) :
    fixedFlavor f t q = f (fun i => q i ⊗ₜ[ℂ] t i) := rfl

def IsInvariant (f : FlavorCoefficient (V := V)) : Prop :=
  (∀ g v, f (fun i => TensorProduct.map (colorAction g) LinearMap.id (v i)) = f v) ∧
  (∀ g v, f (fun i => TensorProduct.map (spinAction g) LinearMap.id (v i)) = f v)

theorem fixedFlavor_invariant (f : FlavorCoefficient (V := V))
    (hf : IsInvariant f) (t : ∀ i, V i) : SixQuarkInvariant.IsInvariant (fixedFlavor f t) := by
  constructor
  · intro g q
    simpa only [fixedFlavor_apply, TensorProduct.map_tmul, LinearMap.id_apply] using
      hf.1 g (fun i => q i ⊗ₜ[ℂ] t i)
  · intro g q
    simpa only [fixedFlavor_apply, TensorProduct.map_tmul, LinearMap.id_apply] using
      hf.2 g (fun i => q i ⊗ₜ[ℂ] t i)

def flavorCoordinates (f : FlavorCoefficient (V := V)) (t : ∀ i, V i) :=
  coordinates (fixedFlavor f t)

private theorem tensor_update [DecidableEq (Fin 6)] (q : Fin 6 → Quark) (t : ∀ i, V i)
    (i : Fin 6) (x : V i) :
    (fun j => q j ⊗ₜ[ℂ] Function.update t i x j) =
      Function.update (fun j => q j ⊗ₜ[ℂ] t j) i (q i ⊗ₜ[ℂ] x) := by
  classical
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [Function.update_of_ne h]

/-- The fixed-flavor family is multilinear, not merely an arbitrary function. -/
def fixedFlavorMap (f : FlavorCoefficient (V := V)) :
    MultilinearMap ℂ V Coefficient where
  toFun := fixedFlavor f
  map_update_add' t i x y := by
    classical
    ext q
    change f (fun j => q j ⊗ₜ[ℂ] Function.update t i (x + y) j) =
      f (fun j => q j ⊗ₜ[ℂ] Function.update t i x j) +
        f (fun j => q j ⊗ₜ[ℂ] Function.update t i y j)
    have hx := congrArg f (tensor_update q t i x)
    have hy := congrArg f (tensor_update q t i y)
    have hxy := congrArg f (tensor_update q t i (x + y))
    calc
      _ = f (Function.update (fun j => q j ⊗ₜ[ℂ] t j) i
          (q i ⊗ₜ[ℂ] (x + y))) := hxy
      _ = _ := by rw [TensorProduct.tmul_add, f.map_update_add]; exact congrArg₂ (· + ·) hx.symm hy.symm
  map_update_smul' t i z x := by
    classical
    ext q
    change f (fun j => q j ⊗ₜ[ℂ] Function.update t i (z • x) j) =
      z • f (fun j => q j ⊗ₜ[ℂ] Function.update t i x j)
    have hx := congrArg f (tensor_update q t i x)
    have hzx := congrArg f (tensor_update q t i (z • x))
    calc
      _ = f (Function.update (fun j => q j ⊗ₜ[ℂ] t j) i
          (q i ⊗ₜ[ℂ] (z • x))) := hzx
      _ = _ := by rw [TensorProduct.tmul_smul, f.map_update_smul]; exact congrArg (z • ·) hx.symm

/-- All 25 coordinate functions are bundled six-linear flavor tensors. -/
def flavorCoordinatesMap (f : FlavorCoefficient (V := V)) :
    MultilinearMap ℂ V (Fin 5 → Fin 5 → ℂ) :=
  coordinateLinear.compMultilinearMap (fixedFlavorMap f)

@[simp] theorem flavorCoordinatesMap_apply (f : FlavorCoefficient (V := V))
    (t : ∀ i, V i) : flavorCoordinatesMap f t = flavorCoordinates f t := rfl

/-- The 25 scalar contractions become functions of the six flavor inputs. -/
theorem coordinates_formula (f : FlavorCoefficient (V := V)) (hf : IsInvariant f)
    (t : ∀ i, V i) (q : Fin 6 → Quark) :
    f (fun i => q i ⊗ₜ[ℂ] t i) =
      reconstruct (flavorCoordinates f t) q := by
  exact (DFunLike.congr_fun
    (reconstruct_coordinates (fixedFlavor f t) (fixedFlavor_invariant f hf t)) q).symm

theorem pure_ext {f h : FlavorCoefficient (V := V)}
    (he : ∀ (q : Fin 6 → Quark) (t : ∀ i, V i),
      f (fun i => q i ⊗ₜ[ℂ] t i) = h (fun i => q i ⊗ₜ[ℂ] t i)) : f = h := by
  let bq := (Pi.basisFun ℂ (Fin 3)).tensorProduct (Pi.basisFun ℂ (Fin 2))
  let b := fun i => bq.tensorProduct (Module.Basis.ofVectorSpace ℂ (V i))
  apply Module.Basis.ext_multilinear b
  intro idx
  simpa only [b, Module.Basis.tensorProduct_apply'] using
    he (fun i => bq (idx i).1)
      (fun i => Module.Basis.ofVectorSpace ℂ (V i) (idx i).2)

/-- Equality on full tensor-product slots, not only decomposable inputs. -/
theorem eq_of_coordinates {f h : FlavorCoefficient (V := V)}
    (hf : IsInvariant f) (hh : IsInvariant h)
    (hc : flavorCoordinates f = flavorCoordinates h) : f = h := by
  apply pure_ext
  intro q t
  rw [coordinates_formula f hf, coordinates_formula h hh, hc]

variable {H : Type*} [Group H] (r : ∀ i, Representation ℂ H (V i))

def IsResidualInvariant (f : FlavorCoefficient (V := V)) : Prop :=
  ∀ g v, f (fun i => TensorProduct.map LinearMap.id (r i g) (v i)) = f v

def ResidualInvariant (c : MultilinearMap ℂ V (Fin 5 → Fin 5 → ℂ)) : Prop :=
  ∀ g t, c (fun i => r i g (t i)) = c t

/-- The residual action imposes exactly invariance on the flavor tensors. -/
theorem residual_invariance_iff (f : FlavorCoefficient (V := V)) (hf : IsInvariant f) :
    IsResidualInvariant r f ↔ ResidualInvariant r (flavorCoordinatesMap f) := by
  constructor
  · intro hr g t
    have he : fixedFlavor f (fun i => r i g (t i)) = fixedFlavor f t := by
      ext q
      simpa only [fixedFlavor_apply, TensorProduct.map_tmul, LinearMap.id_apply] using
        hr g (fun i => q i ⊗ₜ[ℂ] t i)
    exact congrArg coordinates he
  · intro hr g v
    have he : f.compLinearMap (fun i => TensorProduct.map
        (LinearMap.id : Quark →ₗ[ℂ] Quark) (r i g)) = f := by
      apply pure_ext
      intro q t
      simp only [MultilinearMap.compLinearMap_apply, TensorProduct.map_tmul,
        LinearMap.id_apply]
      rw [coordinates_formula f hf, coordinates_formula f hf]
      exact congrArg (fun c => reconstruct c q) (hr g t)
    exact DFunLike.congr_fun he v

section Assembly

/-- Tensor extension of any 25-tuple of six-linear flavor tensors. -/
def assemble (c : MultilinearMap ℂ V (Fin 5 → Fin 5 → ℂ)) : FlavorCoefficient (V := V) :=
  PiTensorProduct.lift.symm
    ((TensorProduct.lift
      (((PiTensorProduct.lift : Coefficient ≃ₗ[ℂ] ((⨂[ℂ] _ : Fin 6, Quark) →ₗ[ℂ] ℂ)).toLinearMap.comp
        reconstructLinear).comp (PiTensorProduct.lift c)).flip).comp
      IndexedTensorSeparation.equiv.toLinearMap)

theorem assemble_apply (c : MultilinearMap ℂ V (Fin 5 → Fin 5 → ℂ))
    (q : Fin 6 → Quark) (t : ∀ i, V i) :
    assemble c (fun i => q i ⊗ₜ[ℂ] t i) = reconstruct (c t) q := by
  change (TensorProduct.lift _).comp IndexedTensorSeparation.equiv.toLinearMap
    (PiTensorProduct.tprod ℂ (fun i => q i ⊗ₜ[ℂ] t i)) = _
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [IndexedTensorSeparation.equiv_pure (L := fun _ : Fin 6 => Quark) (M := V) q t,
    TensorProduct.lift.tmul]
  simp only [LinearMap.flip_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    PiTensorProduct.lift.tprod]
  rfl

theorem assemble_invariant (c : MultilinearMap ℂ V (Fin 5 → Fin 5 → ℂ)) :
    IsInvariant (assemble c) := by
  constructor
  · intro g v
    have he : (assemble c).compLinearMap
        (fun i => TensorProduct.map (colorAction g) (LinearMap.id : V i →ₗ[ℂ] V i)) = assemble c := by
      apply pure_ext
      intro q t
      change assemble c (fun i => TensorProduct.map (colorAction g)
        (LinearMap.id : V i →ₗ[ℂ] V i) (q i ⊗ₜ[ℂ] t i)) =
          assemble c (fun i => q i ⊗ₜ[ℂ] t i)
      simp only [TensorProduct.map_tmul, LinearMap.id_apply]
      rw [assemble_apply, assemble_apply]
      exact (reconstruct_invariant (c t)).1 g q
    exact DFunLike.congr_fun he v
  · intro g v
    have he : (assemble c).compLinearMap
        (fun i => TensorProduct.map (spinAction g) (LinearMap.id : V i →ₗ[ℂ] V i)) = assemble c := by
      apply pure_ext
      intro q t
      change assemble c (fun i => TensorProduct.map (spinAction g)
        (LinearMap.id : V i →ₗ[ℂ] V i) (q i ⊗ₜ[ℂ] t i)) =
          assemble c (fun i => q i ⊗ₜ[ℂ] t i)
      simp only [TensorProduct.map_tmul, LinearMap.id_apply]
      rw [assemble_apply, assemble_apply]
      exact (reconstruct_invariant (c t)).2 g q
    exact DFunLike.congr_fun he v

theorem coordinates_assemble (c : MultilinearMap ℂ V (Fin 5 → Fin 5 → ℂ)) :
    flavorCoordinates (assemble c) = c := by
  funext t
  have he : fixedFlavor (assemble c) t = reconstruct (c t) := by
    ext q
    exact assemble_apply c q t
  rw [flavorCoordinates, he, coordinates_reconstruct]

theorem assemble_coordinates (f : FlavorCoefficient (V := V)) (hf : IsInvariant f) :
    assemble (flavorCoordinatesMap f) = f := by
  apply pure_ext
  intro q t
  rw [assemble_apply, flavorCoordinatesMap_apply, ← coordinates_formula f hf]
end Assembly
end Dependent

section TypedExchanges
variable {V : Fin 6 → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- A typed exchange only identifies slots of the same species. The supplied
fiber equivalences need not identify the up and down carriers. -/
def TypedExchange (g : Fin 4) := ∀ i, V (slotSwap g i) ≃ₗ[ℂ] V i

def exchangeFlavor (g : Fin 4) (e : TypedExchange (V := V) g)
    (t : ∀ i, V i) : ∀ i, V i := fun i => e i (t (slotSwap g i))

/-- Exchange on decomposable inputs, retaining the heterogeneous slot types. -/
def IsTypedSwapAlternating (e : ∀ g, TypedExchange (V := V) g)
    (f : FlavorCoefficient (V := V)) : Prop :=
  ∀ g (q : Fin 6 → Quark) (t : ∀ i, V i),
    f (fun i => q (slotSwap g i) ⊗ₜ[ℂ] exchangeFlavor g (e g) t i) =
    -f (fun i => q i ⊗ₜ[ℂ] t i)

def SatisfiesTypedStatistics (e : ∀ g, TypedExchange (V := V) g)
    (c : (∀ i, V i) → Fin 5 → Fin 5 → ℂ) : Prop :=
  ∀ g t, transform (c (exchangeFlavor g (e g) t)) g = -c t

theorem typed_statistics_iff (e : ∀ g, TypedExchange (V := V) g)
    (f : FlavorCoefficient (V := V)) (hf : IsInvariant f) :
    IsTypedSwapAlternating e f ↔ SatisfiesTypedStatistics e (flavorCoordinates f) := by
  have hrec (t : ∀ i, V i) : reconstruct (flavorCoordinates f t) = fixedFlavor f t :=
    reconstruct_coordinates (fixedFlavor f t) (fixedFlavor_invariant f hf t)
  have hinj : Function.Injective reconstructLinear := by
    intro c d h
    have hc := congrArg coordinates h
    simpa only [reconstructLinear, LinearMap.coe_mk, AddHom.coe_mk,
      coordinates_reconstruct] using hc
  have transfer (g : Fin 4) (t : ∀ i, V i) :
      transform (flavorCoordinates f (exchangeFlavor g (e g) t)) g = -flavorCoordinates f t ↔
      (fixedFlavor f (exchangeFlavor g (e g) t)).domDomCongr (slotSwap g) = -fixedFlavor f t := by
    have h := StatisticalCompleteness.relation_iff reconstructLinear hinj
      (fun k => k.domDomCongr (slotSwap g)) (fun c => transform c g)
      (fun c => reconstruct_transform c g) (-1 : ℂ)
      (flavorCoordinates f (exchangeFlavor g (e g) t)) (flavorCoordinates f t)
    simpa only [neg_one_smul, reconstructLinear, LinearMap.coe_mk,
      AddHom.coe_mk, hrec] using h
  constructor
  · intro ha g t
    apply (transfer g t).mpr
    ext q
    exact ha g q t
  · intro hc g q t
    have he := (transfer g t).mp (hc g t)
    exact DFunLike.congr_fun he q
end TypedExchanges

section Exchanges
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def IsSwapAlternating (f : FlavorCoefficient (V := fun _ => V)) : Prop :=
  ∀ g : Fin 4, f.domDomCongr (slotSwap g) = -f

def IsSpeciesAlternating (f : FlavorCoefficient (V := fun _ => V)) : Prop :=
  ∀ p : Equiv.Perm (Fin 6), SixSlotAlternation.PreservesPattern p →
    ∀ v, f (v ∘ p) = Equiv.Perm.sign p • f v

theorem swaps_iff_species (f : FlavorCoefficient (V := fun _ => V)) :
    IsSwapAlternating f ↔ IsSpeciesAlternating f := by
  constructor
  · intro h p hp v
    apply generators_species_sign f _ p hp v
    intro g x
    exact DFunLike.congr_fun (h g) x
  · intro h g
    ext v
    have hp : SixSlotAlternation.PreservesPattern (slotSwap g) := by
      fin_cases g <;> decide
    have he := h (slotSwap g) hp v
    fin_cases g <;> simpa [slotSwap, Function.comp_def] using he

/-- Simultaneously permute flavor inputs and the color/Weyl coordinates. -/
def SatisfiesFlavorStatistics (c : (Fin 6 → V) → Fin 5 → Fin 5 → ℂ) : Prop :=
  ∀ g t, transform (c (t ∘ slotSwap g)) g = -c t

private theorem reconstruct_neg (c : Fin 5 → Fin 5 → ℂ) :
    reconstruct (-c) = -reconstruct c := by
  simp [reconstruct, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]

/-- Necessity and sufficiency of the four simultaneous exchange equations.
Unlike the one-generation kernel equations, flavor inputs must move too. -/
theorem statistics_iff (f : FlavorCoefficient (V := fun _ => V)) (hf : IsInvariant f) :
    IsSwapAlternating f ↔ SatisfiesFlavorStatistics (flavorCoordinates f) := by
  have hrec (t : Fin 6 → V) : reconstruct (flavorCoordinates f t) = fixedFlavor f t :=
    reconstruct_coordinates (fixedFlavor f t) (fixedFlavor_invariant f hf t)
  constructor
  · intro ha g t
    have he : reconstruct (transform (flavorCoordinates f (t ∘ slotSwap g)) g) =
        reconstruct (-flavorCoordinates f t) := by
      rw [reconstruct_transform, hrec, reconstruct_neg, hrec]
      ext q
      exact DFunLike.congr_fun (ha g) (fun i => q i ⊗ₜ[ℂ] t i)
    have hc := congrArg coordinates he
    simpa only [coordinates_reconstruct] using hc
  · intro hc g
    have he (t : Fin 6 → V) :
        (fixedFlavor f (t ∘ slotSwap g)).domDomCongr (slotSwap g) = -fixedFlavor f t := by
      rw [← hrec (t ∘ slotSwap g), ← reconstruct_transform, hc g t,
        reconstruct_neg, hrec]
    apply pure_ext
    intro q t
    exact DFunLike.congr_fun (he t) q
end Exchanges
end
end GUT.SixQuarkFlavorCoordinates
