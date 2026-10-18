import GUT.SU5.SelectionRules.ResidualSectors
import Physics.StandardModel.Gauge.ResidualGaugeTensor
import Physics.StandardModel.Operators.StandardModelLocalOperator

open Math

/-!
# SM fields realized inside actual residual-character multiplets

Each field map is injective, intertwines the full SM covering action, and
carries the residual character obtained from the actual multiplicity action.
The maps are constructed from the checked SU(5) branching equivalences.
All five fields here are left-handed: up, down and electron are conjugates.
-/

set_option autoImplicit false

namespace GUT.SU5.SupportedFields

noncomputable section

open MatterSource ResidualSectors StandardSMGaugeTensor SMEpsilonTensor
open FiniteAbelianChargeSectors StandardBranchProtonObstruction

variable {H : Type*} [CommGroup H] {n : ℕ}

structure Mode (R : OrdinaryAction H n) (i : Kind) where
  character : H →* Circle
  vector : Generations n
  nonzero : vector ≠ 0
  eigen : ∀ h, representation R i h vector = (character h : ℂ) • vector

theorem mode_exists (R : OrdinaryAction H n) (hn : 0 < n) (i : Kind) : Nonempty (Mode R i) := by
  obtain ⟨chi, v, hv, he⟩ := exists_sector R hn i
  exact ⟨⟨chi, v, hv, he⟩⟩

structure Realization (R : OrdinaryAction H n)
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (sigma : Representation ℂ GaugeGroup W) (chi : H →* Circle) where
  embedding : W →ₗ[ℂ] Space n
  injective : Function.Injective embedding
  gauge : ∀ g x, embedding (sigma g x) = MatterSource.gauge n (StandardModelEmbedding.hom g) (embedding x)
  residual : ∀ h x, (R h).val.val (embedding x) = (chi h : ℂ) • embedding x

def realize {R : OrdinaryAction H n} {i : Kind} (M : Mode R i)
    {W : Type*} [AddCommGroup W] [Module ℂ W] {sigma : Representation ℂ GaugeGroup W}
    (f : Representation.IntertwiningMap sigma ((constituent i).comp StandardModelEmbedding.hom))
    (hf : Function.Injective f) : Realization R sigma M.character where
  embedding := (copy i M.vector).comp f.toLinearMap
  injective := (copy_injective i M.vector M.nonzero).comp hf
  gauge g x := by
    change copy i M.vector (f (sigma g x)) = _
    rw [f.isIntertwining _ _ g x]
    exact (copy_gauge i M.vector _ _).symm
  residual h x := copy_residual R i M.character M.vector M.eigen h (f x)

open Representation.IntertwiningMap in
def quarkIn : Representation.IntertwiningMap quark
    (UnitaryMatter.ten.toRepresentation.comp StandardModelEmbedding.hom) :=
  UnitaryBranching.tenEquiv.symm.toIntertwiningMap.comp
    ((inr ℂ upRight.dual (quark.prod electronRight.dual)).comp
      (inl ℂ quark electronRight.dual))

open Representation.IntertwiningMap in
def upIn : Representation.IntertwiningMap upRight.dual
    (UnitaryMatter.ten.toRepresentation.comp StandardModelEmbedding.hom) :=
  UnitaryBranching.tenEquiv.symm.toIntertwiningMap.comp
    (inl ℂ upRight.dual (quark.prod electronRight.dual))

open Representation.IntertwiningMap in
def electronIn : Representation.IntertwiningMap electronRight.dual
    (UnitaryMatter.ten.toRepresentation.comp StandardModelEmbedding.hom) :=
  UnitaryBranching.tenEquiv.symm.toIntertwiningMap.comp
    ((inr ℂ upRight.dual (quark.prod electronRight.dual)).comp
      (inr ℂ quark electronRight.dual))

open Representation.IntertwiningMap in
def downIn : Representation.IntertwiningMap downRight.dual
    (UnitaryMatter.antifundamental.toRepresentation.comp StandardModelEmbedding.hom) :=
  UnitaryBranching.antifundamentalEquiv.symm.toIntertwiningMap.comp (inl ℂ downRight.dual lepton)

open Representation.IntertwiningMap in
def leptonIn : Representation.IntertwiningMap lepton
    (UnitaryMatter.antifundamental.toRepresentation.comp StandardModelEmbedding.hom) :=
  UnitaryBranching.antifundamentalEquiv.symm.toIntertwiningMap.comp (inr ℂ downRight.dual lepton)

theorem quarkIn_injective : Function.Injective quarkIn := by
  intro x y h
  have h' := UnitaryBranching.tenEquiv.symm.injective h
  exact congrArg (fun p : ExteriorSquareBranching.Blocks => p.2.1) h'

theorem upIn_injective : Function.Injective upIn := by
  intro x y h
  have h' := UnitaryBranching.tenEquiv.symm.injective h
  exact congrArg (fun p : ExteriorSquareBranching.Blocks => p.1) h'

theorem electronIn_injective : Function.Injective electronIn := by
  intro x y h
  have h' := UnitaryBranching.tenEquiv.symm.injective h
  exact congrArg (fun p : ExteriorSquareBranching.Blocks => p.2.2) h'

theorem downIn_injective : Function.Injective downIn := by
  intro x y h
  have h' := UnitaryBranching.antifundamentalEquiv.symm.injective h
  exact congrArg (fun p : FundamentalBranching.BarBlocks => p.1) h'

theorem leptonIn_injective : Function.Injective leptonIn := by
  intro x y h
  have h' := UnitaryBranching.antifundamentalEquiv.symm.injective h
  exact congrArg (fun p : FundamentalBranching.BarBlocks => p.2) h'

def quarkField {R : OrdinaryAction H n} (M : Mode R .ten) : Realization R quark M.character :=
  realize M quarkIn quarkIn_injective
def upField {R : OrdinaryAction H n} (M : Mode R .ten) : Realization R upRight.dual M.character :=
  realize M upIn upIn_injective
def electronField {R : OrdinaryAction H n} (M : Mode R .ten) : Realization R electronRight.dual M.character :=
  realize M electronIn electronIn_injective
def downField {R : OrdinaryAction H n} (M : Mode R .barFive) : Realization R downRight.dual M.character :=
  realize M downIn downIn_injective
def leptonField {R : OrdinaryAction H n} (M : Mode R .barFive) : Realization R lepton M.character :=
  realize M leptonIn leptonIn_injective

def charges {R : OrdinaryAction H n} (T : Mode R .ten) (B : Mode R .barFive) :
    Charges (ChargeLabel H) :=
  ⟨Additive.ofMul T.character, Additive.ofMul T.character, Additive.ofMul B.character,
    Additive.ofMul B.character, Additive.ofMul T.character⟩

theorem charges_compatible {R : OrdinaryAction H n} (T : Mode R .ten) (B : Mode R .barFive) :
    SU5OrbitCompatible (charges T B) := ⟨rfl, rfl, rfl⟩

/-- Actual field support, not nonzero coefficients in a virtual polynomial. -/
structure Support (R : OrdinaryAction H n) (k : Charges (ChargeLabel H)) where
  quark : Realization R StandardSMGaugeTensor.quark k.quark.toMul
  up : Realization R upRight.dual k.up.toMul
  electron : Realization R electronRight.dual k.electron.toMul
  down : Realization R downRight.dual k.down.toMul
  lepton : Realization R StandardSMGaugeTensor.lepton k.lepton.toMul

def support {R : OrdinaryAction H n} (T : Mode R .ten) (B : Mode R .barFive) :
    Support R (charges T B) :=
  ⟨quarkField T, upField T, electronField T, downField B, leptonField B⟩

theorem exists_supported_compatible (R : OrdinaryAction H n) (hn : 0 < n) :
    ∃ k : Charges (ChargeLabel H), Nonempty (Support R k) ∧ SU5OrbitCompatible k := by
  obtain ⟨T⟩ := mode_exists R hn .ten
  obtain ⟨B⟩ := mode_exists R hn .barFive
  exact ⟨charges T B, ⟨support T B⟩, charges_compatible T B⟩

theorem supported_invariant_coordinate_tensors (R : OrdinaryAction H n) (hn : 0 < n) :
    ∃ k : Charges (ChargeLabel H), Nonempty (Support R k) ∧
      qque ≠ 0 ∧ duql ≠ 0 ∧
      (∀ g x, qque (StandardSMResidualTensor.qqueRepresentation k g x) = qque x) ∧
      (∀ g x, duql (StandardSMResidualTensor.duqlRepresentation k g x) = duql x) := by
  obtain ⟨k, hs, hk⟩ := exists_supported_compatible R hn
  exact ⟨k, hs, StandardSMResidualTensor.invariant_tensors_of_su5OrbitCompatible k hk⟩

/-- Both neutral signatures have actual field support. The signature's
Lorentz counts do not assert nonvanishing in a Grassmann algebra. -/
theorem supported_neutral_signatures (R : OrdinaryAction H n) (hn : 0 < n) :
    ∃ k : Charges (ChargeLabel H), Nonempty (Support R k) ∧
      StandardModelLocalOperator.IsPhysicalDeltaBOneOperator StandardModelLocalOperator.qqueOperator ∧
      StandardModelLocalOperator.IsPhysicalDeltaBOneOperator StandardModelLocalOperator.duqlOperator ∧
      StandardModelLocalOperator.operatorCharge k StandardModelLocalOperator.qqueOperator = 0 ∧
      StandardModelLocalOperator.operatorCharge k StandardModelLocalOperator.duqlOperator = 0 := by
  obtain ⟨k, hs, hk⟩ := exists_supported_compatible R hn
  obtain ⟨h1, h2⟩ := proton_functionals_eq_zero_of_su5OrbitCompatible k hk
  exact ⟨k, hs, StandardModelLocalOperator.qque_isPhysicalDeltaBOneOperator,
    StandardModelLocalOperator.duql_isPhysicalDeltaBOneOperator,
    (StandardModelLocalOperator.qque_operatorCharge k).trans h1,
    (StandardModelLocalOperator.duql_operatorCharge k).trans h2⟩

end

end GUT.SU5.SupportedFields
