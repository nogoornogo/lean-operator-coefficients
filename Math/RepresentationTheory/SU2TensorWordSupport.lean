import Math.RepresentationTheory.SU2ClebschGordan
import Math.RepresentationTheory.FiniteExternalProducts
import Math.RepresentationTheory.FiniteProductHomSupport
import Math.RepresentationTheory.Characters.CompactCoefficientSupport
import Math.LinearAlgebra.SymmetricPowerLowDegree

/-! Actual tensor-word branching by finite Clebsch--Gordan paths. The path
degrees decide target occurrence without calculating any multiplicity. -/
namespace Math.SU2TensorWordSupport
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor WeakDoubletScalars
open scoped TensorProduct

inductive Word
  | leaf (degree : ℕ)
  | tensor (left right : Word)

structure Data where
  Carrier : Type
  [additive : AddCommGroup Carrier]
  [linear : Module ℂ Carrier]
  action : Representation ℂ TauCeti.SU2 Carrier
attribute [instance] Data.additive Data.linear

def data : Word → Data
  | .leaf n =>
    { Carrier := Sym[ℂ]^n Doublet
      additive := Module.addCommMonoidToAddCommGroup ℂ
      action := doublet.symmetricPower n }
  | .tensor l r =>
    { Carrier := (data l).Carrier ⊗[ℂ] (data r).Carrier
      action := (data l).action.tprod (data r).action }

abbrev Carrier (w : Word) := (data w).Carrier
abbrev action (w : Word) := (data w).action

structure Spectrum where
  Index : Type
  [finite : Fintype Index]
  [decidable : DecidableEq Index]
  degree : Index → ℕ
attribute [instance] Spectrum.finite Spectrum.decidable

def spectrum : Word → Spectrum
  | .leaf n => { Index := Unit, degree := fun _ => n }
  | .tensor l r =>
    { Index := Σ i : (spectrum l).Index × (spectrum r).Index,
        SU2ClebschGordan.Index ((spectrum l).degree i.1) ((spectrum r).degree i.2)
      degree := fun i => SU2ClebschGordan.degree
        ((spectrum l).degree i.1.1) ((spectrum r).degree i.1.2) i.2 }

abbrev Path (w : Word) := (spectrum w).Index
abbrev degree (w : Word) := (spectrum w).degree

@[reducible] local instance (n : ℕ) : AddCommGroup (Sym[ℂ]^n Doublet) :=
  Module.addCommMonoidToAddCommGroup ℂ

def piece (w : Word) (i : Path w) := doublet.symmetricPower (degree w i)

def singleton (n : ℕ) : Representation.Equiv (doublet.symmetricPower n)
    (FiniteBlockHom.action (fun _ : Unit => doublet.symmetricPower n)) where
  toLinearEquiv :=
    { toFun := fun x _ => x
      invFun := fun x => x ()
      left_inv _ := rfl
      right_inv x := funext (fun i => congrArg x (Subsingleton.elim () i))
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := rfl

def equivalence : (w : Word) → Representation.Equiv (action w) (FiniteBlockHom.action (piece w))
  | .leaf n => singleton n
  | .tensor l r =>
    (tensorEquiv (equivalence l) (equivalence r)).trans
      ((FiniteExternalProducts.diagonalEquivalence (piece l) (piece r)).trans
        ((FiniteExternalProducts.along (fun i : Path l × Path r =>
          (SU2ClebschGordan.equivalence (degree l i.1) (degree r i.2)).symm)).trans
            (FiniteExternalProducts.flatten (fun (i : Path l × Path r)
              (j : SU2ClebschGordan.Index (degree l i.1) (degree r i.2)) =>
                SU2ClebschGordan.summand (degree l i.1) (degree r i.2) j))))

theorem symmetric_hom_iff (a b : ℕ) : SelectionCriteria.Allowed
    (IntertwiningMap (doublet.symmetricPower a) (doublet.symmetricPower b)) ↔ a=b := by
  constructor
  · rintro ⟨f,hf⟩
    have he := (f.ofBijective ((IsIrreducible.bijective_or_eq_zero f).resolve_right hf)).finrank_eq
    rw [TauCeti.SU2.finrank_symPower,TauCeti.SU2.finrank_symPower] at he
    omega
  · rintro rfl
    refine ⟨IntertwiningMap.id _,?_⟩
    intro he
    let : Nontrivial (Sym[ℂ]^a Doublet) := IsIrreducible.nontrivial
      (ρ := doublet.symmetricPower a) inferInstance
    obtain ⟨x,hx⟩ := exists_ne (0 : Sym[ℂ]^a Doublet)
    exact hx (DFunLike.congr_fun he x)

theorem target_iff (w : Word) (n : ℕ) : SelectionCriteria.Allowed
    (IntertwiningMap (action w) (doublet.symmetricPower n)) ↔ ∃ i : Path w, degree w i=n := by
  classical
  rw [SelectionCriteria.allowed_equiv (CompactCoefficientSupport.homEquiv (equivalence w)
    (.refl (doublet.symmetricPower n))),FiniteProductHomSupport.allowed_iff]
  exact exists_congr (fun i => symmetric_hom_iff (degree w i) n)

def Supports (w : Word) : Prop := ∃ i : Path w, degree w i=0

theorem allowed_iff (w : Word) : SelectionCriteria.Allowed
    (InvariantCoefficientTransport.Invariants (action w)) ↔ Supports w :=
  (SelectionCriteria.allowed_equiv (CompactCoefficientSupport.homEquiv (.refl (action w))
    (SymmetricPowerLowDegree.representationZeroEquiv doublet).symm)).trans (target_iff w 0)

theorem forbidden_iff (w : Word) : SelectionCriteria.Forbidden
    (InvariantCoefficientTransport.Invariants (action w)) ↔ ¬ Supports w := by
  rw [SelectionCriteria.forbidden_iff_not_allowed,allowed_iff]

end
end Math.SU2TensorWordSupport
