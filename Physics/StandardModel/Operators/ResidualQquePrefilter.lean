import Physics.StandardModel.Operators.NeutralQqueExterior
import Math.RepresentationTheory.ProtectionConstraintPullback
import Math.RepresentationTheory.Unitary.UnitarySubrepresentationOrthogonality

/-! Necessary residual-action constraints on actual participating light subspaces. -/
namespace GUT.ResidualQquePrefilter
set_option autoImplicit false
noncomputable section
open Math Representation StandardSMGaugeTensor
open StandardBranchProtonObstruction FiniteAbelianChargeSectors
variable {H F : Type} [CommGroup H] [AddCommGroup F] [Module ℂ F]
    (tau : Representation ℂ (GaugeGroup × H) F)

/-- Admission is an actual invariant-subspace dictionary, not a charge table.
UC and EC are left-chiral; physical right-handed fields use their duals. -/
structure Triplet where
  charges : Charges (Math.FiniteAbelianChargeSectors.ChargeLabel H)
  Q : Subrepresentation tau
  UC : Subrepresentation tau
  EC : Subrepresentation tau
  qEquiv : Equiv Q.toRepresentation (NeutralQqueExterior.q charges)
  uEquiv : Equiv UC.toRepresentation
    (StandardSMResidualTensor.charged upRight.dual charges.up.toMul)
  eEquiv : Equiv EC.toRepresentation
    (StandardSMResidualTensor.charged electronRight.dual charges.electron.toMul)

namespace Triplet
variable {tau}
def HasCoefficient (X : Triplet tau) : Prop :=
  ∃ f : QqueSpinorExterior.ExteriorCoefficient X.Q.toRepresentation
    X.UC.toRepresentation.dual X.EC.toRepresentation.dual, f ≠ 0

def rightUpEquiv (X : Triplet tau) :
    Equiv X.UC.toRepresentation.dual (NeutralQqueExterior.u X.charges) := by
  let e := SplitRepresentationProjection.dualEquiv X.uEquiv
  rw [NeutralQqueExterior.charged_dual] at e
  exact e.trans (NeutralQqueExterior.chargedEquiv
    (SplitRepresentationProjection.bidualEquiv upRight).symm _)

def rightElectronEquiv (X : Triplet tau) :
    Equiv X.EC.toRepresentation.dual (NeutralQqueExterior.e X.charges) := by
  let e := SplitRepresentationProjection.dualEquiv X.eEquiv
  rw [NeutralQqueExterior.charged_dual] at e
  exact e.trans (NeutralQqueExterior.chargedEquiv
    (SplitRepresentationProjection.bidualEquiv electronRight).symm _)

theorem neutral_hasCoefficient (X : Triplet tau)
    (h : protonFirstCharacter X.charges = 1) : X.HasCoefficient :=
  NeutralQqueExterior.exists_on_fields X.charges h _ _ _
    X.qEquiv X.rightUpEquiv X.rightElectronEquiv
end Triplet

/-- Prohibition must cover every admitted actual carrier, not merely selected labels. -/
def Forbids (tau : Representation ℂ (GaugeGroup × H) F) : Prop :=
  ∀ X : Triplet tau, ¬ X.HasCoefficient

/-- A necessary condition, not a converse prohibition or UV-existence theorem. -/
def Necessary (tau : Representation ℂ (GaugeGroup × H) F) : Prop :=
  ∀ X : Triplet tau, protonFirstCharacter X.charges ≠ 1

theorem necessary (hp : Forbids tau) : Necessary tau := by
  intro X h
  exact hp X (X.neutral_hasCoefficient h)

theorem neutral_excludes (X : Triplet tau)
    (h : protonFirstCharacter X.charges = 1) : ¬ Forbids tau :=
  fun hp => necessary tau hp X h

theorem equal_species_excludes (X : Triplet tau)
    (hu : X.charges.quark = X.charges.up)
    (he : X.charges.quark = X.charges.electron) : ¬ Forbids tau := by
  apply neutral_excludes tau X
  apply protonFirstCharacter_eq_one_of_eq_zero
  simp [protonFirst, ← hu, ← he]

theorem block_excludes (X : Triplet tau) (a c w : H → Circle)
    (hq : ∀ h, X.charges.quark.toMul h = a h * c h * w h)
    (hu : ∀ h, X.charges.up.toMul h = a h * c h * c h)
    (he : ∀ h, X.charges.electron.toMul h = a h * w h * w h) : ¬ Forbids tau :=
  neutral_excludes tau X (NeutralQqueExterior.neutral_of_pointwise_block X.charges a c w hq hu he)

/-- Twisting a gauge intertwiner by the same character preserves its map. -/
def chargedMap {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {r : Representation ℂ GaugeGroup V} {s : Representation ℂ GaugeGroup W}
    (f : IntertwiningMap r s) (chi : H →* Circle) :
    IntertwiningMap (StandardSMResidualTensor.charged r chi)
      (StandardSMResidualTensor.charged s chi) where
  toLinearMap := f.toLinearMap
  isIntertwining' g := by
    ext v
    change f ((chi g.2 : ℂ) • r g.1 v) = (chi g.2 : ℂ) • s g.1 (f v)
    rw [map_smul]
    exact congrArg (fun x => (chi g.2 : ℂ) • x) (IntertwiningMap.isIntertwining r s f g.1 v)

section Concrete
variable (k : Charges (Math.FiniteAbelianChargeSectors.ChargeLabel H))
local instance : AddCommGroup Quark := inferInstance
abbrev selectedAction := (NeutralQqueExterior.q k).prod
  ((StandardSMResidualTensor.charged upRight.dual k.up.toMul).prod
    (StandardSMResidualTensor.charged electronRight.dual k.electron.toMul))

/-- A concrete regression dictionary is built from actual ranges, without
assuming a coefficient. It contains selected species only, not a full UV model. -/
def selectedTriplet : Triplet (selectedAction k) := by
  let q := NeutralQqueExterior.q k
  let u := StandardSMResidualTensor.charged upRight.dual k.up.toMul
  let e := StandardSMResidualTensor.charged electronRight.dual k.electron.toMul
  let fq := IntertwiningMap.inl ℂ q (u.prod e)
  let fu := (IntertwiningMap.inr ℂ q (u.prod e)).comp (IntertwiningMap.inl ℂ u e)
  let fe := (IntertwiningMap.inr ℂ q (u.prod e)).comp (IntertwiningMap.inr ℂ u e)
  have hq : Function.Injective fq := fun x y h => congrArg Prod.fst h
  have hu : Function.Injective fu := fun x y h => congrArg (fun v => v.2.1) h
  have he : Function.Injective fe := fun x y h => congrArg (fun v => v.2.2) h
  exact ⟨k, fq.range, fu.range, fe.range,
    (UnitarySubrepresentationOrthogonality.rangeEquiv fq hq).symm,
    (UnitarySubrepresentationOrthogonality.rangeEquiv fu hu).symm,
    (UnitarySubrepresentationOrthogonality.rangeEquiv fe he).symm⟩

theorem selected_neutral_reject (h : protonFirstCharacter k = 1) :
    ¬ Forbids (selectedAction k) := neutral_excludes _ (selectedTriplet k) h
end Concrete

section Parameters
variable {P : Type*} (actions : P → Representation ℂ (GaugeGroup × H) F)
    (sm : P → Prop)
/-- Keeps precisely the declared SM predicate and the necessary residual test.
A missing triplet dictionary is not evidence that protection is possible. -/
def retain (p : P) : Prop := sm p ∧ Necessary (actions p)

theorem preserve (p : P) (hs : sm p) (hp : Forbids (actions p)) :
    retain actions sm p := ⟨hs, necessary _ hp⟩

theorem reject (p : P) (X : Triplet (actions p))
    (h : protonFirstCharacter X.charges = 1) : ¬ Forbids (actions p) :=
  neutral_excludes _ X h
/-- A finite supplied carrier list gives a finite test, without pretending
that it enumerates all carriers or that character equality is computable. -/
def selectedRetain {I : Type*} (triplets : ∀ p : P, I → Triplet (actions p)) (p : P) : Prop :=
  sm p ∧ ∀ i, protonFirstCharacter (triplets p i).charges ≠ 1

theorem selected_preserve {I : Type*} (triplets : ∀ p : P, I → Triplet (actions p))
    (p : P) (hs : sm p) (hp : Forbids (actions p)) :
    selectedRetain actions sm triplets p :=
  ⟨hs, fun i => necessary _ hp (triplets p i)⟩

def finiteCandidates [Fintype P] {I : Type*}
    (triplets : ∀ p : P, I → Triplet (actions p))
    [DecidablePred (selectedRetain actions sm triplets)] : Finset P :=
  Finset.univ.filter (selectedRetain actions sm triplets)

theorem finite_preserve [Fintype P] {I : Type*}
    (triplets : ∀ p : P, I → Triplet (actions p))
    [DecidablePred (selectedRetain actions sm triplets)]
    (p : P) (hs : sm p) (hp : Forbids (actions p)) :
    p ∈ finiteCandidates actions sm triplets :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ p, selected_preserve actions sm triplets p hs hp⟩
end Parameters
end
end GUT.ResidualQquePrefilter
