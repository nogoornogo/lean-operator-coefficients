import Physics.StandardModel.Operators.FlavoredCyclicSelection
import Physics.StandardModel.Operators.CyclicResidualSelection

open Math

/-! Kernel-checked finite controls for empty, singleton, trivial and nonuniform
flavor assignments. These are coefficient dimensions, not generation rates. -/
namespace GUT.FlavoredCyclicControls
set_option autoImplicit false
noncomputable section
open FlavoredCyclicSelection FlavoredCyclicCoordinates CyclicWeightCoordinates SelectionCriteria

set_option maxRecDepth 4000 in
theorem trivial_three_generation : Module.finrank ℂ
    (DeltaLOneSignedFields.Sector (flavor (fun _ => Fin 3) (fun _ _ => (0 : ZMod 2))) 1) =
      273 := by
  rw [finrank_total]
  decide +kernel

theorem empty_total : Module.finrank ℂ
    (DeltaLOneSignedFields.Sector (flavor (fun _ => Fin 0) (fun _ _ => (0 : ZMod 2))) 1) =
      0 := by
  rw [finrank_total]
  decide +kernel

theorem empty_weinberg : Module.finrank ℂ
    (WeinbergSMInterface.ModelSector (diagonal (fun _ : Fin 0 => (0 : ZMod 2)))) = 0 := by
  rw [llhh_finrank]
  decide +kernel

abbrev unequalIndex (s : Fin 5) := Fin (![2,1,0,3,1] s)

theorem unequal_species_total : Module.finrank ℂ
    (DeltaLOneSignedFields.Sector (flavor unequalIndex (fun _ _ => (0 : ZMod 2))) 1) =
      21 := by
  rw [finrank_total]
  decide +kernel

def nonuniform (i : Fin 2) : ZMod 2 := if i = 0 then 0 else 1

/-- Four neutral ordered triples reduce to three independent qqql components. -/
theorem nonuniform_qqql : Module.finrank ℂ
    (QqqlExteriorCompleteness.Sector (diagonal nonuniform)
      (diagonal (fun _ : Fin 1 => (0 : ZMod 2)))) = 3 := by
  rw [(QqqlDiagonalCoordinates.equiv (diagonal nonuniform)
    (diagonal (fun _ : Fin 1 => (0 : ZMod 2))) (Pi.basisFun ℂ (Fin 2))
    (Pi.basisFun ℂ (Fin 1)) nonuniform (fun _ => 0)
    (diagonal_weights _) (diagonal_weights _)).finrank_eq]
  rw [Module.finrank_fintype_fun_eq_card]
  decide +kernel

theorem nonuniform_ordered_count : Fintype.card
    {p : Fin 2 × Fin 2 × Fin 2 // nonuniform p.1 + nonuniform p.2.1 +
      nonuniform p.2.2 = 0} = 4 := by decide +kernel

def quarkParity : (s : Fin 5) → Fin 1 → ZMod 2 :=
  fun s _ => CyclicResidualSelection.quarkParity s

theorem singleton_quarkParity_forbidden :
    Forbidden (DeltaLOneSignedFields.Sector (flavor (fun _ => Fin 1) quarkParity) 1) := by
  rw [forbidden_total_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    apply Fintype.card_eq_zero_iff.mp
    simp only [DuqlIndex, QqueIndex, QqqlIndex, DuueIndex, fourCharge, qqueCharge,
      QqqlDiagonalCoordinates.charge, TripleFlavorWeights.charge,
      TripleFlavorWeights.triple, symmetricCharge, quarkParity,
      CyclicResidualSelection.quarkParity]
    decide +kernel

theorem singleton_quarkParity_weinberg :
    Allowed (WeinbergSMInterface.ModelSector (diagonal (quarkParity 3))) := by
  rw [llhh_allowed]
  refine ⟨TauCeti.Sym.ofFn ![0,0], ?_⟩
  rw [symmetricCharge_pair]
  rfl

theorem isEmpty_constant {N : ℕ} {A : Type*} (w : A → ZMod N) (v : ZMod N)
    (a : A) (h : ∀ a, w a = v) : IsEmpty {a // w a = 0} ↔ v ≠ 0 := by
  constructor
  · intro he hz
    exact he.false ⟨a, (h a).trans hz⟩
  · intro hv
    constructor
    rintro ⟨a,ha⟩
    exact hv ((h a).symm.trans ha)

theorem symmetric_constant {N : ℕ} {A : Type*} (v : ZMod N) (s : Sym A 2) :
    symmetricCharge 2 (fun _ : A => v) s = v + v := by
  simp [symmetricCharge, Sym.card_coe]

/-- The general finite theorem recovers the earlier scalar four-family criterion. -/
theorem singleton_forbidden_iff {N : ℕ} [NeZero N] (c : Fin 5 → ZMod N) :
    Forbidden (DeltaLOneSignedFields.Sector
      (flavor (fun _ => Fin 1) (fun s _ => c s)) 1) ↔
      CyclicResidualSelection.familyCharge c 0 ≠ 0 ∧
        CyclicResidualSelection.familyCharge c 1 ≠ 0 ∧
          CyclicResidualSelection.familyCharge c 2 ≠ 0 ∧
            CyclicResidualSelection.familyCharge c 3 ≠ 0 := by
  rw [forbidden_total_iff]
  have hd : IsEmpty (DuqlIndex (fun _ => Fin 1) (fun s _ => c s)) ↔
      CyclicResidualSelection.familyCharge c 0 ≠ 0 :=
    isEmpty_constant _ _ ((0,0),(0,0)) (fun _ => rfl)
  have he : IsEmpty (DuueIndex (fun _ => Fin 1) (fun s _ => c s)) ↔
      CyclicResidualSelection.familyCharge c 3 ≠ 0 :=
    isEmpty_constant _ _ ((0,0),(0,0)) (fun _ => rfl)
  have hq : IsEmpty (QqueIndex (fun _ => Fin 1) (fun s _ => c s)) ↔
      CyclicResidualSelection.familyCharge c 1 ≠ 0 := by
    apply isEmpty_constant _ _ (TauCeti.Sym.ofFn ![0,0], (0,0))
    intro p
    change symmetricCharge 2 (fun _ : Fin 1 => c 0) p.1 + (c 1+c 4) = _
    rw [symmetric_constant]
    rfl
  have ht : IsEmpty (QqqlIndex (fun _ => Fin 1) (fun s _ => c s)) ↔
      CyclicResidualSelection.familyCharge c 2 ≠ 0 := by
    apply isEmpty_constant _ _ (0, Sum.inl ⟨(0,0,0), by decide⟩)
    rintro ⟨t,p⟩
    rcases p with p | (p | (p | ⟨p,r⟩))
    all_goals simp [QqqlDiagonalCoordinates.charge, TripleFlavorWeights.charge,
      TripleFlavorWeights.triple, CyclicResidualSelection.familyCharge, add_assoc]
  rw [hd, hq, ht, he]

theorem singleton_weinberg_iff {N : ℕ} [NeZero N] (l : ZMod N) :
    Allowed (WeinbergSMInterface.ModelSector (diagonal (fun _ : Fin 1 => l))) ↔ l+l=0 := by
  rw [llhh_allowed]
  simp only [symmetric_constant]
  constructor
  · rintro ⟨s,hs⟩; exact hs
  · intro h; exact ⟨TauCeti.Sym.ofFn ![0,0],h⟩

end
end GUT.FlavoredCyclicControls
