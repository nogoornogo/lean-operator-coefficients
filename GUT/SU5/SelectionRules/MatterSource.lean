import GUT.SU5.Representations.MatterIrreducibility
import GUT.SU5.Branching.Unitary
import Math.RepresentationTheory.Multiplicity.ExplicitMultiplicity

open Math

/-!
# Actual finite-generation SU(5) matter and ordinary residual actions

The source is the Hilbert sum of n copies of the actual 10 and n copies of
the actual bar5. An ordinary action is any group homomorphism into its full
unitary SU(5) centralizer. Its two multiplicity actions are derived, not input.
This file does not impose determinant one on the ordinary symmetry.
-/

set_option autoImplicit false

namespace GUT.SU5.MatterSource

noncomputable section

open StandardModelEmbedding

inductive Kind | ten | barFive
  deriving DecidableEq

instance : Fintype Kind := ⟨{.ten, .barFive}, by intro i; cases i <;> simp⟩

def Carrier : Kind → Type
  | .ten => UnitaryMatter.TenHilbert
  | .barFive => UnitaryMatter.BarFiveHilbert

instance carrierNormed : (i : Kind) → NormedAddCommGroup (Carrier i)
  | .ten => inferInstanceAs (NormedAddCommGroup UnitaryMatter.TenHilbert)
  | .barFive => inferInstanceAs (NormedAddCommGroup UnitaryMatter.BarFiveHilbert)
instance carrierInner : (i : Kind) → InnerProductSpace ℂ (Carrier i)
  | .ten => inferInstanceAs (InnerProductSpace ℂ UnitaryMatter.TenHilbert)
  | .barFive => inferInstanceAs (InnerProductSpace ℂ UnitaryMatter.BarFiveHilbert)
instance carrierFinite : (i : Kind) → FiniteDimensional ℂ (Carrier i)
  | .ten => inferInstanceAs (FiniteDimensional ℂ UnitaryMatter.TenHilbert)
  | .barFive => inferInstanceAs (FiniteDimensional ℂ UnitaryMatter.BarFiveHilbert)

def constituent : (i : Kind) → Representation ℂ TargetGroup (Carrier i)
  | .ten => UnitaryMatter.ten.toRepresentation
  | .barFive => UnitaryMatter.antifundamental.toRepresentation

theorem constituent_irreducible (i : Kind) : (constituent i).IsIrreducible := by
  cases i
  · exact MatterIrreducibility.unitary_ten_irreducible
  · exact MatterIrreducibility.unitary_antifundamental_irreducible

instance carrierNontrivial (i : Kind) : Nontrivial (Carrier i) :=
  (constituent_irreducible i).nontrivial

theorem constituent_inequivalent (i j : Kind) (hij : i ≠ j) :
    IsEmpty (Representation.Equiv (constituent j) (constituent i)) := by
  cases i <;> cases j
  · exact (hij rfl).elim
  · exact ⟨fun e => MatterIrreducibility.unitary_ten_not_equiv_barFive.false e.symm⟩
  · exact MatterIrreducibility.unitary_ten_not_equiv_barFive
  · exact (hij rfl).elim

theorem constituent_unitary (i : Kind) :
    UnitaryMultiplicity.IsUnitaryRepresentation (constituent i) := by
  cases i
  · exact UnitaryMatter.ten_unitary.inner_map_map
  · exact UnitaryMatter.antifundamental_unitary.inner_map_map

theorem constituent_jointlyContinuous (i : Kind) :
    Continuous (fun p : TargetGroup × Carrier i => constituent i p.1 p.2) := by
  cases i
  · exact (UnitaryMatter.ten_continuous.comp continuous_fst).clm_apply continuous_snd
  · exact (UnitaryMatter.antifundamental_continuous.comp continuous_fst).clm_apply continuous_snd

abbrev Space (n : ℕ) := ExplicitMultiplicity.Space (fun _ : Kind => n) Carrier

def gauge (n : ℕ) : Representation ℂ TargetGroup (Space n) :=
  ExplicitMultiplicity.action (fun _ => n) Carrier constituent

theorem gauge_unitary (n : ℕ) : UnitaryMultiplicity.IsUnitaryRepresentation (gauge n) :=
  ExplicitMultiplicity.action_unitary (fun _ => n) Carrier constituent constituent_unitary

theorem gauge_jointlyContinuous (n : ℕ) :
    Continuous (fun p : TargetGroup × Space n => gauge n p.1 p.2) := by
  change Continuous (fun p : TargetGroup × Space n =>
    WithLp.toLp 2 fun i => WithLp.toLp 2 fun a => constituent i p.1 (p.2 i a))
  refine (PiLp.continuous_toLp _ _).comp (continuous_pi fun i => ?_)
  refine (PiLp.continuous_toLp _ _).comp (continuous_pi fun a => ?_)
  have heval : Continuous (fun x : Space n => x i a) :=
    (PiLp.continuous_apply 2 (fun _ : Fin n => Carrier i) a).comp
      (PiLp.continuous_apply 2 (fun j : Kind => PiLp 2 (fun _ : Fin n => Carrier j)) i)
  exact (constituent_jointlyContinuous i).comp
    (continuous_fst.prodMk (heval.comp continuous_snd))

abbrev Factors (n : ℕ) := Kind → Matrix.unitaryGroup (Fin n) ℂ

def centralizerEquiv (n : ℕ) : Factors n ≃ₜ*
    UnitaryCentralizerTransport.unitaryCentralizer (gauge n) :=
  ExplicitMultiplicity.unitaryEquiv (fun _ => n) Carrier constituent
    constituent_irreducible constituent_inequivalent

abbrev OrdinaryAction (H : Type*) [Group H] (n : ℕ) :=
  H →* UnitaryCentralizerTransport.unitaryCentralizer (gauge n)

variable {H : Type*} [Group H] {n : ℕ}

def multiplicityAction (R : OrdinaryAction H n) : H →* Factors n :=
  (centralizerEquiv n).symm.toMonoidHom.comp R

def sectorAction (R : OrdinaryAction H n) (i : Kind) :
    H →* Matrix.unitaryGroup (Fin n) ℂ where
  toFun h := multiplicityAction R h i
  map_one' := congrFun (multiplicityAction R).map_one i
  map_mul' h k := congrFun ((multiplicityAction R).map_mul h k) i

theorem action_eq_multiplicity (R : OrdinaryAction H n) (h : H)
    (x : Space n) (i : Kind) (a : Fin n) :
    (R h).val.val x i a = ∑ b, (sectorAction R i h).val a b • x i b :=
  ExplicitMultiplicity.unitaryEquiv_symm_action (fun _ => n) Carrier constituent
    constituent_irreducible constituent_inequivalent (R h) x i a

def ofFactors (A : H →* Factors n) : OrdinaryAction H n :=
  (centralizerEquiv n).toMonoidHom.comp A

@[simp] theorem multiplicityAction_ofFactors (A : H →* Factors n) :
    multiplicityAction (ofFactors A) = A := by
  apply MonoidHom.ext
  intro h
  exact (centralizerEquiv n).symm_apply_apply (A h)

@[simp] theorem ofFactors_multiplicityAction (R : OrdinaryAction H n) :
    ofFactors (multiplicityAction R) = R := by
  apply MonoidHom.ext
  intro h
  exact (centralizerEquiv n).apply_symm_apply (R h)

end

end GUT.SU5.MatterSource
