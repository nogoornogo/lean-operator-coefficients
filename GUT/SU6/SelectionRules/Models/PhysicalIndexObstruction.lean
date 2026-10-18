import GUT.SU6.SelectionRules.Models.PhysicalChainSource
import GUT.SU6.SelectionRules.Models.FiniteIndexCertificate

open Math
namespace GUT.SU6PhysicalIndexObstruction
set_option autoImplicit false
noncomputable section
open FiniteChargeProfiles FiniteAbelianChargeSectors StandardBranchProtonObstruction
open InvariantWeylMass UnitaryVirtualRealization

/-- A positive singleton profile determines its charge, independently of its size. -/
theorem single_charge_eq {A : Type*} (a b : A) (N : ℕ) (hN : 0 < N)
    (h : Finsupp.single a N = Finsupp.single b N) : a = b := by
  classical
  by_contra hn
  have he := congrArg (fun p : A →₀ ℕ => p a) h
  simp [hn] at he
  omega

variable {H : Type*} [CommGroup H]
  (R : ActualUnitaryGroupRepresentation (ChargedAmbientRealization.AmbientGroup H))
  (B : SymmetricMass (SU6.PhysicalChainSource.physicalFields R).rho)

/-- Actual physical mass elimination derives profile equality; it is not an input. -/
theorem profiles_compatible (P : Profiles (ChargeLabel H)) (s : ChargeLabel H →₀ ℤ)
    (ht : ProfileZeroModeSupport.HasTarget (SU6.PhysicalChainSource.physicalFields R) B P s) :
    OrbitCompatible P :=
  SU5.TorusMassSource.profiles_compatible
    (StandardChain.pullback SU6.StandardSU5Inclusion.inclusion R.rho)
    (SU6.PhysicalChainSource.mass R B) P s
    (SU6.PhysicalChainSource.hasTarget R B P s ht)

/-- A positive pure light target must have equal Q, U and E residual characters. -/
theorem pure_charge_equalities (N : ℕ) (hN : 0 < N) (k : Charges (ChargeLabel H))
    (s : ChargeLabel H →₀ ℤ)
    (ht : ProfileZeroModeSupport.HasTarget (SU6.PhysicalChainSource.physicalFields R) B
      (pure N k) s) : k.quark = k.up ∧ k.quark = k.electron := by
  have hc := profiles_compatible R B (pure N k) s ht
  exact ⟨single_charge_eq _ _ N hN hc.1, single_charge_eq _ _ N hN hc.2.1⟩

/-- Every positive pure target has neutral qque character. This is an
arbitrary-character extraction of the existing profile equalities, not an
assertion that a torus profile supplies actual full-SM light fields. -/
theorem pure_qque_neutral (N : ℕ) (hN : 0 < N) (k : Charges (ChargeLabel H))
    (s : ChargeLabel H →₀ ℤ)
    (ht : ProfileZeroModeSupport.HasTarget (SU6.PhysicalChainSource.physicalFields R) B
      (pure N k) s) : protonFirstCharacter k = 1 := by
  obtain ⟨hu, he⟩ := pure_charge_equalities R B N hN k s ht
  apply protonFirstCharacter_eq_one_of_eq_zero
  simp [protonFirst, ← hu, ← he]

/-- All copy counts and all invariant symmetric masses are covered through
the arbitrary actual unitary ambient representation. No Z5 restriction. -/
theorem no_pure_nontrivial_target (N : ℕ) (hN : 0 < N)
    (k : Charges (ChargeLabel H)) (s : ChargeLabel H →₀ ℤ)
    (hk : protonFirstCharacter k ≠ 1) :
    ¬ ProfileZeroModeSupport.HasTarget (SU6.PhysicalChainSource.physicalFields R) B
      (pure N k) s := by
  intro ht
  exact hk (pure_qque_neutral R B N hN k s ht)

/-- Mapping additive search charges into genuine residual characters. -/
def searchCharges (f : ZMod 5 → ChargeLabel H) (x y h : ZMod 5) : Charges (ChargeLabel H) :=
  ⟨f x, f (-x-h), f (-x+h), f y, f (-y+h)⟩

theorem no_search_target (f : ZMod 5 → ChargeLabel H) (hf : Function.Injective f)
    (x y h : ZMod 5) (hq : SU6CyclicPatternSearch.qque x y h ≠ 0)
    (N : ℕ) (hN : 0 < N) (s : ChargeLabel H →₀ ℤ) :
    ¬ ProfileZeroModeSupport.HasTarget (SU6.PhysicalChainSource.physicalFields R) B
      (pure N (searchCharges f x y h)) s := by
  intro ht
  obtain ⟨hu, he⟩ := pure_charge_equalities R B N hN (searchCharges f x y h) s ht
  have hU : x = -x-h := hf hu
  have hE : x = -y+h := hf he
  apply hq
  unfold SU6CyclicPatternSearch.qque
  rw [← hU, ← hE]
  ring

/-- Genuine faithful characters of the residual Z5 group, in additive notation. -/
def cyclicLabel (q : ZMod 5) : ChargeLabel (CyclicCharge.Group 5) :=
  Additive.ofMul {
    toFun := fun g => ZMod.toCircle (q * Multiplicative.toAdd g)
    map_one' := by simp
    map_mul' := by intro g h; simp [mul_add, AddChar.map_add_eq_mul] }

theorem cyclicLabel_injective : Function.Injective cyclicLabel := by
  intro a b he
  have h := congrArg (fun c : ChargeLabel (CyclicCharge.Group 5) =>
    c.toMul (Multiplicative.ofAdd (1 : ZMod 5))) he
  apply ZMod.injective_toCircle
  simpa [cyclicLabel] using h

/-- Five normalized search representatives; Q=x, L=1-3x, H=3x-1. -/
def normalizedCharges (x : Fin 5) : Charges (ChargeLabel (CyclicCharge.Group 5)) :=
  searchCharges cyclicLabel (x.val : ZMod 5) (1-3*(x.val : ZMod 5))
    (3*(x.val : ZMod 5)-1)

/-- The physical character target uses exactly the earlier finite target charges. -/
theorem normalized_dictionary (x : Fin 5) :
    (SU6FiniteIndexCertificate.lightProfile x).map
      (fun t => (t.1.val : ZMod 5)) =
    [(x.val : ZMod 5), -(x.val : ZMod 5)-(3*(x.val : ZMod 5)-1),
      -(x.val : ZMod 5)+(3*(x.val : ZMod 5)-1),
      1-3*(x.val : ZMod 5), -(1-3*(x.val : ZMod 5))+(3*(x.val : ZMod 5)-1)] := by
  revert x
  decide +kernel

theorem no_normalized_target
    (R : ActualUnitaryGroupRepresentation
      (ChargedAmbientRealization.AmbientGroup (CyclicCharge.Group 5)))
    (B : SymmetricMass (SU6.PhysicalChainSource.physicalFields R).rho)
    (x : Fin 5) (N : ℕ) (hN : 0 < N)
    (s : ChargeLabel (CyclicCharge.Group 5) →₀ ℤ) :
    ¬ ProfileZeroModeSupport.HasTarget (SU6.PhysicalChainSource.physicalFields R) B
      (pure N (normalizedCharges x)) s := by
  apply no_search_target R B cyclicLabel cyclicLabel_injective
    (x.val : ZMod 5) (1-3*(x.val : ZMod 5)) (3*(x.val : ZMod 5)-1) _ N hN s
  rw [SU6CyclicPatternSearch.qque_simplify]
  have he : 3*(x.val : ZMod 5)+(1-3*(x.val : ZMod 5)) = 1 := by ring
  rw [he]
  decide

end
end GUT.SU6PhysicalIndexObstruction
