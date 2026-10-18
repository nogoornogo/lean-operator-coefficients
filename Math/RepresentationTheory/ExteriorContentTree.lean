import Math.RepresentationTheory.SumPatternExterior
import Math.RepresentationTheory.ConstantPatternExterior
import Math.RepresentationTheory.ExternalInvariantTensor
import Math.RepresentationTheory.PatternCoefficientSupport
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RepresentationTheory.Character

/-! Finite-tree iteration of actual selected statistical-source decompositions. -/
namespace Math.ExteriorContentTree
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
universe u v
variable (G : Type v) [Group G]

structure Leaf : Type (max (u+1) v) where
  Carrier : Type u
  [additive : AddCommGroup Carrier]
  [linear : Module ℂ Carrier]
  rho : Representation ℂ G Carrier
  degree : ℕ
attribute [instance] Leaf.additive Leaf.linear

inductive Content : Type (max (u+1) v) where
  | leaf (data : Leaf.{u} G)
  | node (left right : Content)

variable {G}
abbrev Species : Content.{u} G → Type
  | .leaf _ => Unit
  | .node l r => Species l ⊕ Species r
instance speciesFinite (c : Content.{u} G) : Fintype (Species c) :=
  match c with | .leaf _ => inferInstance | .node l r => letI := speciesFinite l; letI := speciesFinite r; inferInstance
instance speciesDecidable (c : Content.{u} G) : DecidableEq (Species c) :=
  match c with | .leaf _ => inferInstance | .node l r => letI := speciesDecidable l; letI := speciesDecidable r; inferInstance

abbrev Fields : (c : Content.{u} G) → Species c → Type u
  | .leaf a, _ => a.Carrier
  | .node l r, a => SumPatternExterior.Fields (V := Fields l) (W := Fields r) a
instance fieldsAdditive (c : Content.{u} G) : ∀ a, AddCommGroup (Fields c a) :=
  match c with
  | .leaf data => fun _ => data.additive
  | .node l r => @SumPatternExterior.instAddCommGroupFields (Species l) (Species r)
      (Fields l) (Fields r) (fieldsAdditive l) (fieldsAdditive r)
instance fieldsLinear (c : Content.{u} G) : ∀ a, Module ℂ (Fields c a) :=
  match c with
  | .leaf data => fun _ => data.linear
  | .node l r => @SumPatternExterior.instModuleComplexFields (Species l) (Species r)
      (Fields l) (Fields r) (fieldsAdditive l) (fieldsLinear l) (fieldsAdditive r) (fieldsLinear r)

def fields : (c : Content.{u} G) → ∀ a, Representation ℂ G (Fields c a)
  | .leaf a, _ => a.rho
  | .node l r, a => match a with | .inl s => fields l s | .inr t => fields r t

def degree : Content.{u} G → ℕ
  | .leaf a => a.degree
  | .node l r => degree l + degree r

def pattern : (c : Content.{u} G) → Fin (degree c) → Species c
  | .leaf _, _ => ()
  | .node l r, i => SumPatternExterior.pattern (pattern l) (pattern r) i

abbrev statistical (c : Content.{u} G) :=
  @PatternExteriorSource.representation (Species c) G (speciesFinite c) (speciesDecidable c)
    inferInstance (Fields c) (fieldsAdditive c) (fieldsLinear c) (fields c) (degree c) (pattern c)

def factorData : Content.{u} G → Leaf.{u} G
  | .leaf a =>
      { Carrier := ⋀[ℂ]^a.degree a.Carrier
        rho := a.rho.exteriorPower a.degree
        degree := a.degree }
  | .node l r =>
      { Carrier := (factorData l).Carrier ⊗[ℂ] (factorData r).Carrier
        rho := (factorData l).rho.tprod (factorData r).rho
        degree := degree l + degree r }

abbrev Carrier (c : Content.{u} G) := (factorData c).Carrier
abbrev factor (c : Content.{u} G) := (factorData c).rho

def nodeTransport (l r : Content.{u} G) : Representation.Equiv
    (PatternExteriorSource.representation (SumPatternExterior.fields (fields l) (fields r))
      (SumPatternExterior.pattern (pattern l) (pattern r)))
    (statistical (.node l r)) where
  toLinearEquiv :=
    { toFun := fun x => ⟨x.val,x.property⟩
      invFun := fun x => ⟨x.val,x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change exteriorPower.map (degree l + degree r)
      ((FiniteSpeciesExterior.representation (SumPatternExterior.fields (fields l) (fields r))) g) x.val =
      exteriorPower.map (degree l + degree r) ((FiniteSpeciesExterior.representation (fields (.node l r))) g) x.val
    have he : (FiniteSpeciesExterior.representation (SumPatternExterior.fields (fields l) (fields r))) g =
        (FiniteSpeciesExterior.representation (fields (.node l r))) g := by
      apply LinearMap.ext
      intro v
      funext a
      cases a <;> rfl
    rw [he]

def decomposition : (c : Content.{u} G) → Representation.Equiv (factor c)
    (statistical c)
  | .leaf a => ConstantPatternExterior.equiv (fields (.leaf a)) () a.degree
  | .node l r => (ExternalInvariantTensor.tensorEquiv (decomposition l) (decomposition r)).trans
      ((SumPatternExterior.equiv (fields l) (fields r) (pattern l) (pattern r)).trans (nodeTransport l r))

def FiniteLeaves : Content.{u} G → Prop
  | .leaf a => Module.Finite ℂ a.Carrier
  | .node l r => FiniteLeaves l ∧ FiniteLeaves r

def dimensionFormula : Content.{u} G → ℕ
  | .leaf a => (Module.finrank ℂ a.Carrier).choose a.degree
  | .node l r => dimensionFormula l * dimensionFormula r

theorem carrier_finite (c : Content.{u} G) (h : FiniteLeaves c) : Module.Finite ℂ (Carrier c) := by
  induction c with
  | leaf a =>
    have : Module.Finite ℂ a.Carrier := h
    change Module.Finite ℂ (⋀[ℂ]^a.degree a.Carrier)
    infer_instance
  | node l r hl hr =>
    have : Module.Finite ℂ (Carrier l) := hl h.1
    have : Module.Finite ℂ (Carrier r) := hr h.2
    change Module.Finite ℂ (Carrier l ⊗[ℂ] Carrier r)
    infer_instance

theorem carrier_dimension (c : Content.{u} G) (h : FiniteLeaves c) :
    Module.finrank ℂ (Carrier c) = dimensionFormula c := by
  induction c with
  | leaf a =>
    have : Module.Finite ℂ a.Carrier := h
    exact exteriorPower.finrank_eq ℂ a.Carrier a.degree
  | node l r hl hr =>
    have : Module.Finite ℂ (Carrier l) := carrier_finite l h.1
    have : Module.Finite ℂ (Carrier r) := carrier_finite r h.2
    change Module.finrank ℂ (Carrier l ⊗[ℂ] Carrier r) = dimensionFormula l * dimensionFormula r
    rw [Module.finrank_tensorProduct,hl h.1,hr h.2]

theorem source_dimension (c : Content.{u} G) (h : FiniteLeaves c) :
    Module.finrank ℂ (PatternExteriorSource.Source (fields c) (pattern c)) = dimensionFormula c :=
  (decomposition c).finrank_eq.symm.trans (carrier_dimension c h)

variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]

def withSpectator (c : Content.{u} G) (b : Representation ℂ G Y) :=
  ExternalInvariantTensor.tensorEquiv (decomposition c) (Representation.Equiv.refl b)

def coefficientEquiv (c : Content.{u} G) (b : Representation ℂ G Y) :
    PatternCoefficientSupport.space (fields c) (pattern c) b ≃ₗ[ℂ]
      InvariantCoefficientTransport.Invariants ((factor c).tprod b) :=
  (PatternCoefficientSupport.equiv (fields c) (pattern c) b).trans
    (InvariantCoefficientTransport.alongEquiv (withSpectator c b)).symm

def characterFormula : Content.{u} G → G → ℂ
  | .leaf a, g => (a.rho.exteriorPower a.degree).character g
  | .node l r, g => characterFormula l g * characterFormula r g

theorem factor_character (c : Content.{u} G) (h : FiniteLeaves c) (g : G) :
    (factor c).character g = characterFormula c g := by
  induction c with
  | leaf a => rfl
  | node l r hl hr =>
    have : Module.Finite ℂ (Carrier l) := carrier_finite l h.1
    have : Module.Finite ℂ (Carrier r) := carrier_finite r h.2
    change ((factor l).tprod (factor r)).character g = characterFormula l g * characterFormula r g
    rw [Representation.char_tensor]
    exact congrArg₂ (· * ·) (hl h.1) (hr h.2)

theorem source_character (c : Content.{u} G) (h : FiniteLeaves c) (g : G) :
    (statistical c).character g = characterFormula c g :=
  (congrFun (Representation.char_iso (decomposition c)) g).symm.trans (factor_character c h g)

end
end Math.ExteriorContentTree
