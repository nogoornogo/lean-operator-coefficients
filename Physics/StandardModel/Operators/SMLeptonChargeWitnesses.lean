import Physics.StandardModel.Operators.SMCompactSupportDecision
import Physics.StandardModel.Operators.SMChargeDegreeBounds

/-! Explicit full joint-support witnesses for every capacity/parity candidate
lepton charge at B3=3 or 6. Rendered by finite-charge-witnesses.py; every
declaration is checked by the normal library build. No CSV/table premise. -/
namespace GUT.SMLeptonChargeWitnesses
open Math GUT

open Math GUT
attribute [local instance] SMCompactSupportDecision.expressionDecision
attribute [local instance] SMCompactSupportDecision.jointDecision

-- Explicit witnesses avoid enumerating all occupations on positive queries.
def indexedOccupationChoice {G : Type*} [Group G] (k : Nat)
    (a : Fin (k+1) → ExteriorContentTree.Leaf G)
    (o : ∀ i, GenerationTensorSupport.Occupation (a i).degree) :
    GenerationTensorSupport.Choice (IndexedExteriorContent.tree k a) :=
  match k with
  | 0 => o 0
  | k+1 => (o 0, indexedOccupationChoice k (fun i => a i.succ) (fun i => o i.succ))

def pickOccupation (n a b : Nat) (ha : a<n+1) (hb : b<n-a+1) :
    GenerationTensorSupport.Occupation n :=
  CompactGenerationOccupations.toOccupation n ⟨⟨a,ha⟩,⟨b,hb⟩⟩

noncomputable def constantOccupationChoice (s : DeltaLOneSignedInput.Species) (n a b : Nat)
    (ha : a<n+1) (hb : b<n-a+1) :
    GenerationTensorSupport.Choice
      (SMJointContentSupport.tree (fun t => if t=s then n else 0)) := by
  apply indexedOccupationChoice 9 (SMJointContentSupport.leaves (fun t => if t=s then n else 0))
  intro t
  dsimp only [SMJointContentSupport.leaves]
  change GenerationTensorSupport.Occupation (if t=s then n else 0)
  exact pickOccupation (if t=s then n else 0) (if t=s then a else 0)
    (if t=s then b else 0) (by split_ifs <;> omega) (by split_ifs <;> omega)

-- A candidate branch is data, not an assumed occurrence. Its existence and
-- full joint validity are checked separately in every closed certificate.
def firstChoice : (e : JointSourceExpression.Expr) → Option (JointSourceExpression.Choice e)
  | .zero => none
  | .atom _ => some ()
  | .sum l r => match firstChoice l with
    | some i => some (.inl i)
    | none => (firstChoice r).map Sum.inr
  | .tensor l r => do
    let i ← firstChoice l
    let j ← firstChoice r
    pure (i,j)

def firstBranch (e : JointSourceExpression.Expr) (h : (firstChoice e).isSome = true) :
    JointSourceExpression.Choice e := (firstChoice e).get (by simpa using h)
noncomputable def balanced (c : DeltaLOneSignedInput.Species → Nat) :
    GenerationTensorSupport.Choice (SMJointContentSupport.tree c) := by
  apply indexedOccupationChoice 9 (SMJointContentSupport.leaves c)
  intro t
  exact pickOccupation (c t) (c t / 3) ((c t + 1) / 3) (by omega) (by omega)

def w3_n17_counts : DeltaLOneSignedInput.Species → Nat := ![1,0,12,0,0,0,10,0,12,5]
def w3_n17_pattern (i : Fin 40) : DeltaLOneSignedInput.Species := if i.val < 1 then 0 else if i.val < 13 then 2 else if i.val < 23 then 6 else if i.val < 35 then 8 else if i.val < 40 then 9 else 0
theorem w3_n17_counts_eq : SMIteratedContent.counts w3_n17_pattern = w3_n17_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w3_n17_support : SMJointContentSupport.Supports w3_n17_counts 1 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w3_n17_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w3_n17_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w3_n17_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  refine ⟨40, w3_n17_pattern, 0, 1, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_n17_pattern q l 0 1).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨1, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 1 1; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w3_n17_counts_eq]
  exact w3_n17_support

theorem w3_n17_charges : SMQLPatternRequests.blCharge w3_n17_pattern = (3,-17) := by
  decide +kernel

theorem w3_n17_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (-17 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  apply w3_n17_allowed
  rw [SMChargeDegreeBounds.residual_linear, w3_n17_charges]
  simpa using hc

theorem w3_n17_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (-17 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(3,-17)) := by
  refine ⟨40, w3_n17_pattern, 0, 1, w3_n17_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_n17_pattern q l 0 1).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨1, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w3_n17_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 1 1
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w3_n17_counts_eq]
    exact w3_n17_support

def w3_n15_counts : DeltaLOneSignedInput.Species → Nat := ![1,0,10,0,0,0,8,0,12,3]
def w3_n15_pattern (i : Fin 34) : DeltaLOneSignedInput.Species := if i.val < 1 then 0 else if i.val < 11 then 2 else if i.val < 19 then 6 else if i.val < 31 then 8 else if i.val < 34 then 9 else 0
theorem w3_n15_counts_eq : SMIteratedContent.counts w3_n15_pattern = w3_n15_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w3_n15_support : SMJointContentSupport.Supports w3_n15_counts 1 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w3_n15_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w3_n15_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w3_n15_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  refine ⟨34, w3_n15_pattern, 0, 1, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_n15_pattern q l 0 1).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨1, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 1 1; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w3_n15_counts_eq]
  exact w3_n15_support

theorem w3_n15_charges : SMQLPatternRequests.blCharge w3_n15_pattern = (3,-15) := by
  decide +kernel

theorem w3_n15_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (-15 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  apply w3_n15_allowed
  rw [SMChargeDegreeBounds.residual_linear, w3_n15_charges]
  simpa using hc

theorem w3_n15_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (-15 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(3,-15)) := by
  refine ⟨34, w3_n15_pattern, 0, 1, w3_n15_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_n15_pattern q l 0 1).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨1, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w3_n15_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 1 1
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w3_n15_counts_eq]
    exact w3_n15_support

def w3_n13_counts : DeltaLOneSignedInput.Species → Nat := ![1,0,8,0,0,0,6,0,12,1]
def w3_n13_pattern (i : Fin 28) : DeltaLOneSignedInput.Species := if i.val < 1 then 0 else if i.val < 9 then 2 else if i.val < 15 then 6 else if i.val < 27 then 8 else if i.val < 28 then 9 else 0
theorem w3_n13_counts_eq : SMIteratedContent.counts w3_n13_pattern = w3_n13_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w3_n13_support : SMJointContentSupport.Supports w3_n13_counts 1 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w3_n13_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w3_n13_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w3_n13_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  refine ⟨28, w3_n13_pattern, 0, 1, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_n13_pattern q l 0 1).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨1, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 1 1; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w3_n13_counts_eq]
  exact w3_n13_support

theorem w3_n13_charges : SMQLPatternRequests.blCharge w3_n13_pattern = (3,-13) := by
  decide +kernel

theorem w3_n13_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (-13 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  apply w3_n13_allowed
  rw [SMChargeDegreeBounds.residual_linear, w3_n13_charges]
  simpa using hc

theorem w3_n13_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (-13 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(3,-13)) := by
  refine ⟨28, w3_n13_pattern, 0, 1, w3_n13_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_n13_pattern q l 0 1).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨1, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w3_n13_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 1 1
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w3_n13_counts_eq]
    exact w3_n13_support

def w3_n11_counts : DeltaLOneSignedInput.Species → Nat := ![0,1,8,0,0,0,6,0,11,0]
def w3_n11_pattern (i : Fin 26) : DeltaLOneSignedInput.Species := if i.val < 1 then 1 else if i.val < 9 then 2 else if i.val < 15 then 6 else if i.val < 26 then 8 else 0
theorem w3_n11_counts_eq : SMIteratedContent.counts w3_n11_pattern = w3_n11_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w3_n11_support : SMJointContentSupport.Supports w3_n11_counts 1 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w3_n11_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w3_n11_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w3_n11_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  refine ⟨26, w3_n11_pattern, 1, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_n11_pattern q l 1 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨1, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 1 0 1; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w3_n11_counts_eq]
  exact w3_n11_support

theorem w3_n11_charges : SMQLPatternRequests.blCharge w3_n11_pattern = (3,-11) := by
  decide +kernel

theorem w3_n11_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (-11 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  apply w3_n11_allowed
  rw [SMChargeDegreeBounds.residual_linear, w3_n11_charges]
  simpa using hc

theorem w3_n11_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (-11 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(3,-11)) := by
  refine ⟨26, w3_n11_pattern, 1, 0, w3_n11_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_n11_pattern q l 1 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨1, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w3_n11_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 1 0 1
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w3_n11_counts_eq]
    exact w3_n11_support

def w3_n9_counts : DeltaLOneSignedInput.Species → Nat := ![0,1,6,0,0,0,4,0,9,0]
def w3_n9_pattern (i : Fin 20) : DeltaLOneSignedInput.Species := if i.val < 1 then 1 else if i.val < 7 then 2 else if i.val < 11 then 6 else if i.val < 20 then 8 else 0
theorem w3_n9_counts_eq : SMIteratedContent.counts w3_n9_pattern = w3_n9_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w3_n9_support : SMJointContentSupport.Supports w3_n9_counts 1 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w3_n9_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w3_n9_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w3_n9_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  refine ⟨20, w3_n9_pattern, 0, 1, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_n9_pattern q l 0 1).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨1, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 1 1; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w3_n9_counts_eq]
  exact w3_n9_support

theorem w3_n9_charges : SMQLPatternRequests.blCharge w3_n9_pattern = (3,-9) := by
  decide +kernel

theorem w3_n9_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (-9 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  apply w3_n9_allowed
  rw [SMChargeDegreeBounds.residual_linear, w3_n9_charges]
  simpa using hc

theorem w3_n9_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (-9 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(3,-9)) := by
  refine ⟨20, w3_n9_pattern, 0, 1, w3_n9_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_n9_pattern q l 0 1).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨1, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w3_n9_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 1 1
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w3_n9_counts_eq]
    exact w3_n9_support

def w3_n7_counts : DeltaLOneSignedInput.Species → Nat := ![0,1,6,0,0,0,4,0,7,0]
def w3_n7_pattern (i : Fin 18) : DeltaLOneSignedInput.Species := if i.val < 1 then 1 else if i.val < 7 then 2 else if i.val < 11 then 6 else if i.val < 18 then 8 else 0
theorem w3_n7_counts_eq : SMIteratedContent.counts w3_n7_pattern = w3_n7_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w3_n7_support : SMJointContentSupport.Supports w3_n7_counts 1 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w3_n7_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w3_n7_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w3_n7_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  refine ⟨18, w3_n7_pattern, 1, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_n7_pattern q l 1 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨1, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 1 0 1; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w3_n7_counts_eq]
  exact w3_n7_support

theorem w3_n7_charges : SMQLPatternRequests.blCharge w3_n7_pattern = (3,-7) := by
  decide +kernel

theorem w3_n7_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (-7 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  apply w3_n7_allowed
  rw [SMChargeDegreeBounds.residual_linear, w3_n7_charges]
  simpa using hc

theorem w3_n7_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (-7 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(3,-7)) := by
  refine ⟨18, w3_n7_pattern, 1, 0, w3_n7_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_n7_pattern q l 1 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨1, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w3_n7_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 1 0 1
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w3_n7_counts_eq]
    exact w3_n7_support

def w3_n5_counts : DeltaLOneSignedInput.Species → Nat := ![0,1,4,0,0,0,2,0,5,0]
def w3_n5_pattern (i : Fin 12) : DeltaLOneSignedInput.Species := if i.val < 1 then 1 else if i.val < 5 then 2 else if i.val < 7 then 6 else if i.val < 12 then 8 else 0
theorem w3_n5_counts_eq : SMIteratedContent.counts w3_n5_pattern = w3_n5_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w3_n5_support : SMJointContentSupport.Supports w3_n5_counts 1 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w3_n5_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w3_n5_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w3_n5_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  refine ⟨12, w3_n5_pattern, 0, 1, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_n5_pattern q l 0 1).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨1, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 1 1; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w3_n5_counts_eq]
  exact w3_n5_support

theorem w3_n5_charges : SMQLPatternRequests.blCharge w3_n5_pattern = (3,-5) := by
  decide +kernel

theorem w3_n5_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (-5 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  apply w3_n5_allowed
  rw [SMChargeDegreeBounds.residual_linear, w3_n5_charges]
  simpa using hc

theorem w3_n5_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (-5 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(3,-5)) := by
  refine ⟨12, w3_n5_pattern, 0, 1, w3_n5_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_n5_pattern q l 0 1).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨1, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w3_n5_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 1 1
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w3_n5_counts_eq]
    exact w3_n5_support

def w3_n3_counts : DeltaLOneSignedInput.Species → Nat := ![0,1,4,0,0,0,2,0,3,0]
def w3_n3_pattern (i : Fin 10) : DeltaLOneSignedInput.Species := if i.val < 1 then 1 else if i.val < 5 then 2 else if i.val < 7 then 6 else if i.val < 10 then 8 else 0
theorem w3_n3_counts_eq : SMIteratedContent.counts w3_n3_pattern = w3_n3_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w3_n3_support : SMJointContentSupport.Supports w3_n3_counts 1 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w3_n3_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w3_n3_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w3_n3_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  refine ⟨10, w3_n3_pattern, 1, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_n3_pattern q l 1 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨1, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 1 0 1; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w3_n3_counts_eq]
  exact w3_n3_support

theorem w3_n3_charges : SMQLPatternRequests.blCharge w3_n3_pattern = (3,-3) := by
  decide +kernel

theorem w3_n3_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (-3 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  apply w3_n3_allowed
  rw [SMChargeDegreeBounds.residual_linear, w3_n3_charges]
  simpa using hc

theorem w3_n3_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (-3 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(3,-3)) := by
  refine ⟨10, w3_n3_pattern, 1, 0, w3_n3_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_n3_pattern q l 1 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨1, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w3_n3_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 1 0 1
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w3_n3_counts_eq]
    exact w3_n3_support

def w3_n1_counts : DeltaLOneSignedInput.Species → Nat := ![0,1,2,0,0,0,0,0,1,0]
def w3_n1_pattern (i : Fin 4) : DeltaLOneSignedInput.Species := if i.val < 1 then 1 else if i.val < 3 then 2 else if i.val < 4 then 8 else 0
theorem w3_n1_counts_eq : SMIteratedContent.counts w3_n1_pattern = w3_n1_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w3_n1_support : SMJointContentSupport.Supports w3_n1_counts 1 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w3_n1_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w3_n1_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w3_n1_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  refine ⟨4, w3_n1_pattern, 0, 1, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_n1_pattern q l 0 1).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨1, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 1 1; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w3_n1_counts_eq]
  exact w3_n1_support

theorem w3_n1_charges : SMQLPatternRequests.blCharge w3_n1_pattern = (3,-1) := by
  decide +kernel

theorem w3_n1_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (-1 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  apply w3_n1_allowed
  rw [SMChargeDegreeBounds.residual_linear, w3_n1_charges]
  simpa using hc

theorem w3_n1_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (-1 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(3,-1)) := by
  refine ⟨4, w3_n1_pattern, 0, 1, w3_n1_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_n1_pattern q l 0 1).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨1, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w3_n1_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 1 1
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w3_n1_counts_eq]
    exact w3_n1_support

def w3_p1_counts : DeltaLOneSignedInput.Species → Nat := ![3,0,0,1,0,0,0,0,0,0]
def w3_p1_pattern (i : Fin 4) : DeltaLOneSignedInput.Species := if i.val < 3 then 0 else if i.val < 4 then 3 else 0
theorem w3_p1_counts_eq : SMIteratedContent.counts w3_p1_pattern = w3_p1_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w3_p1_support : SMJointContentSupport.Supports w3_p1_counts 0 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w3_p1_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w3_p1_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w3_p1_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  refine ⟨4, w3_p1_pattern, 0, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_p1_pattern q l 0 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨0, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 0 0; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w3_p1_counts_eq]
  exact w3_p1_support

theorem w3_p1_charges : SMQLPatternRequests.blCharge w3_p1_pattern = (3,1) := by
  decide +kernel

theorem w3_p1_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (1 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  apply w3_p1_allowed
  rw [SMChargeDegreeBounds.residual_linear, w3_p1_charges]
  simpa using hc

theorem w3_p1_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (1 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(3,1)) := by
  refine ⟨4, w3_p1_pattern, 0, 0, w3_p1_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_p1_pattern q l 0 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨0, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w3_p1_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 0 0
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w3_p1_counts_eq]
    exact w3_p1_support

def w3_p3_counts : DeltaLOneSignedInput.Species → Nat := ![3,0,0,3,0,0,0,0,0,0]
def w3_p3_pattern (i : Fin 6) : DeltaLOneSignedInput.Species := if i.val < 3 then 0 else if i.val < 6 then 3 else 0
theorem w3_p3_counts_eq : SMIteratedContent.counts w3_p3_pattern = w3_p3_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w3_p3_support : SMJointContentSupport.Supports w3_p3_counts 2 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w3_p3_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w3_p3_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w3_p3_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  refine ⟨6, w3_p3_pattern, 2, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_p3_pattern q l 2 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨2, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 2 0 2; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w3_p3_counts_eq]
  exact w3_p3_support

theorem w3_p3_charges : SMQLPatternRequests.blCharge w3_p3_pattern = (3,3) := by
  decide +kernel

theorem w3_p3_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (3 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  apply w3_p3_allowed
  rw [SMChargeDegreeBounds.residual_linear, w3_p3_charges]
  simpa using hc

theorem w3_p3_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (3 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(3,3)) := by
  refine ⟨6, w3_p3_pattern, 2, 0, w3_p3_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_p3_pattern q l 2 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨2, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w3_p3_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 2 0 2
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w3_p3_counts_eq]
    exact w3_p3_support

def w3_p5_counts : DeltaLOneSignedInput.Species → Nat := ![3,2,0,5,0,0,0,2,0,0]
def w3_p5_pattern (i : Fin 12) : DeltaLOneSignedInput.Species := if i.val < 3 then 0 else if i.val < 5 then 1 else if i.val < 10 then 3 else if i.val < 12 then 7 else 0
theorem w3_p5_counts_eq : SMIteratedContent.counts w3_p5_pattern = w3_p5_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w3_p5_support : SMJointContentSupport.Supports w3_p5_counts 0 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w3_p5_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w3_p5_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w3_p5_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  refine ⟨12, w3_p5_pattern, 0, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_p5_pattern q l 0 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨0, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 0 0; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w3_p5_counts_eq]
  exact w3_p5_support

theorem w3_p5_charges : SMQLPatternRequests.blCharge w3_p5_pattern = (3,5) := by
  decide +kernel

theorem w3_p5_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (5 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  apply w3_p5_allowed
  rw [SMChargeDegreeBounds.residual_linear, w3_p5_charges]
  simpa using hc

theorem w3_p5_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (5 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(3,5)) := by
  refine ⟨12, w3_p5_pattern, 0, 0, w3_p5_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_p5_pattern q l 0 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨0, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w3_p5_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 0 0
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w3_p5_counts_eq]
    exact w3_p5_support

def w3_p7_counts : DeltaLOneSignedInput.Species → Nat := ![3,2,0,7,0,0,0,2,0,0]
def w3_p7_pattern (i : Fin 14) : DeltaLOneSignedInput.Species := if i.val < 3 then 0 else if i.val < 5 then 1 else if i.val < 12 then 3 else if i.val < 14 then 7 else 0
theorem w3_p7_counts_eq : SMIteratedContent.counts w3_p7_pattern = w3_p7_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w3_p7_support : SMJointContentSupport.Supports w3_p7_counts 2 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w3_p7_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w3_p7_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w3_p7_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  refine ⟨14, w3_p7_pattern, 2, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_p7_pattern q l 2 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨2, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 2 0 2; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w3_p7_counts_eq]
  exact w3_p7_support

theorem w3_p7_charges : SMQLPatternRequests.blCharge w3_p7_pattern = (3,7) := by
  decide +kernel

theorem w3_p7_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (7 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  apply w3_p7_allowed
  rw [SMChargeDegreeBounds.residual_linear, w3_p7_charges]
  simpa using hc

theorem w3_p7_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (7 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(3,7)) := by
  refine ⟨14, w3_p7_pattern, 2, 0, w3_p7_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_p7_pattern q l 2 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨2, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w3_p7_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 2 0 2
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w3_p7_counts_eq]
    exact w3_p7_support

def w3_p9_counts : DeltaLOneSignedInput.Species → Nat := ![3,4,0,9,0,0,0,4,0,0]
def w3_p9_pattern (i : Fin 20) : DeltaLOneSignedInput.Species := if i.val < 3 then 0 else if i.val < 7 then 1 else if i.val < 16 then 3 else if i.val < 20 then 7 else 0
theorem w3_p9_counts_eq : SMIteratedContent.counts w3_p9_pattern = w3_p9_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w3_p9_support : SMJointContentSupport.Supports w3_p9_counts 0 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w3_p9_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w3_p9_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w3_p9_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  refine ⟨20, w3_p9_pattern, 0, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_p9_pattern q l 0 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨0, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 0 0; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w3_p9_counts_eq]
  exact w3_p9_support

theorem w3_p9_charges : SMQLPatternRequests.blCharge w3_p9_pattern = (3,9) := by
  decide +kernel

theorem w3_p9_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (9 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  apply w3_p9_allowed
  rw [SMChargeDegreeBounds.residual_linear, w3_p9_charges]
  simpa using hc

theorem w3_p9_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (9 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(3,9)) := by
  refine ⟨20, w3_p9_pattern, 0, 0, w3_p9_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_p9_pattern q l 0 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨0, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w3_p9_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 0 0
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w3_p9_counts_eq]
    exact w3_p9_support

def w3_p11_counts : DeltaLOneSignedInput.Species → Nat := ![3,4,0,11,0,0,0,4,0,0]
def w3_p11_pattern (i : Fin 22) : DeltaLOneSignedInput.Species := if i.val < 3 then 0 else if i.val < 7 then 1 else if i.val < 18 then 3 else if i.val < 22 then 7 else 0
theorem w3_p11_counts_eq : SMIteratedContent.counts w3_p11_pattern = w3_p11_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w3_p11_support : SMJointContentSupport.Supports w3_p11_counts 2 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w3_p11_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w3_p11_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w3_p11_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  refine ⟨22, w3_p11_pattern, 2, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_p11_pattern q l 2 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨2, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 2 0 2; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w3_p11_counts_eq]
  exact w3_p11_support

theorem w3_p11_charges : SMQLPatternRequests.blCharge w3_p11_pattern = (3,11) := by
  decide +kernel

theorem w3_p11_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (11 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  apply w3_p11_allowed
  rw [SMChargeDegreeBounds.residual_linear, w3_p11_charges]
  simpa using hc

theorem w3_p11_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (11 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(3,11)) := by
  refine ⟨22, w3_p11_pattern, 2, 0, w3_p11_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_p11_pattern q l 2 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨2, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w3_p11_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 2 0 2
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w3_p11_counts_eq]
    exact w3_p11_support

def w3_p13_counts : DeltaLOneSignedInput.Species → Nat := ![1,7,0,12,1,0,0,5,0,0]
def w3_p13_pattern (i : Fin 26) : DeltaLOneSignedInput.Species := if i.val < 1 then 0 else if i.val < 8 then 1 else if i.val < 20 then 3 else if i.val < 21 then 4 else if i.val < 26 then 7 else 0
theorem w3_p13_counts_eq : SMIteratedContent.counts w3_p13_pattern = w3_p13_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w3_p13_support : SMJointContentSupport.Supports w3_p13_counts 1 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w3_p13_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w3_p13_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w3_p13_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  refine ⟨26, w3_p13_pattern, 1, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_p13_pattern q l 1 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨1, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 1 0 1; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w3_p13_counts_eq]
  exact w3_p13_support

theorem w3_p13_charges : SMQLPatternRequests.blCharge w3_p13_pattern = (3,13) := by
  decide +kernel

theorem w3_p13_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (13 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  apply w3_p13_allowed
  rw [SMChargeDegreeBounds.residual_linear, w3_p13_charges]
  simpa using hc

theorem w3_p13_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (13 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(3,13)) := by
  refine ⟨26, w3_p13_pattern, 1, 0, w3_p13_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_p13_pattern q l 1 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨1, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w3_p13_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 1 0 1
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w3_p13_counts_eq]
    exact w3_p13_support

def w3_p15_counts : DeltaLOneSignedInput.Species → Nat := ![1,9,0,12,3,0,0,7,0,0]
def w3_p15_pattern (i : Fin 32) : DeltaLOneSignedInput.Species := if i.val < 1 then 0 else if i.val < 10 then 1 else if i.val < 22 then 3 else if i.val < 25 then 4 else if i.val < 32 then 7 else 0
theorem w3_p15_counts_eq : SMIteratedContent.counts w3_p15_pattern = w3_p15_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w3_p15_support : SMJointContentSupport.Supports w3_p15_counts 1 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w3_p15_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w3_p15_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w3_p15_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  refine ⟨32, w3_p15_pattern, 1, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_p15_pattern q l 1 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨1, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 1 0 1; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w3_p15_counts_eq]
  exact w3_p15_support

theorem w3_p15_charges : SMQLPatternRequests.blCharge w3_p15_pattern = (3,15) := by
  decide +kernel

theorem w3_p15_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (15 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  apply w3_p15_allowed
  rw [SMChargeDegreeBounds.residual_linear, w3_p15_charges]
  simpa using hc

theorem w3_p15_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (15 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(3,15)) := by
  refine ⟨32, w3_p15_pattern, 1, 0, w3_p15_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_p15_pattern q l 1 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨1, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w3_p15_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 1 0 1
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w3_p15_counts_eq]
    exact w3_p15_support

def w3_p17_counts : DeltaLOneSignedInput.Species → Nat := ![1,11,0,12,5,0,0,9,0,0]
def w3_p17_pattern (i : Fin 38) : DeltaLOneSignedInput.Species := if i.val < 1 then 0 else if i.val < 12 then 1 else if i.val < 24 then 3 else if i.val < 29 then 4 else if i.val < 38 then 7 else 0
theorem w3_p17_counts_eq : SMIteratedContent.counts w3_p17_pattern = w3_p17_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w3_p17_support : SMJointContentSupport.Supports w3_p17_counts 1 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w3_p17_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w3_p17_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w3_p17_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  refine ⟨38, w3_p17_pattern, 1, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_p17_pattern q l 1 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨1, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 1 0 1; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w3_p17_counts_eq]
  exact w3_p17_support

theorem w3_p17_charges : SMQLPatternRequests.blCharge w3_p17_pattern = (3,17) := by
  decide +kernel

theorem w3_p17_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (17 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) := by
  apply w3_p17_allowed
  rw [SMChargeDegreeBounds.residual_linear, w3_p17_charges]
  simpa using hc

theorem w3_p17_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q + (17 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(3,17)) := by
  refine ⟨38, w3_p17_pattern, 1, 0, w3_p17_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w3_p17_pattern q l 1 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨1, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w3_p17_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 1 0 1
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w3_p17_counts_eq]
    exact w3_p17_support

def w6_n18_counts : DeltaLOneSignedInput.Species → Nat := ![0,0,16,0,0,0,10,0,12,6]
def w6_n18_pattern (i : Fin 44) : DeltaLOneSignedInput.Species := if i.val < 16 then 2 else if i.val < 26 then 6 else if i.val < 38 then 8 else if i.val < 44 then 9 else 0
theorem w6_n18_counts_eq : SMIteratedContent.counts w6_n18_pattern = w6_n18_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w6_n18_support : SMJointContentSupport.Supports w6_n18_counts 0 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w6_n18_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w6_n18_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w6_n18_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  refine ⟨44, w6_n18_pattern, 0, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_n18_pattern q l 0 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨0, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 0 0; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w6_n18_counts_eq]
  exact w6_n18_support

theorem w6_n18_charges : SMQLPatternRequests.blCharge w6_n18_pattern = (6,-18) := by
  decide +kernel

theorem w6_n18_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (-18 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  apply w6_n18_allowed
  rw [SMChargeDegreeBounds.residual_linear, w6_n18_charges]
  simpa using hc

theorem w6_n18_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (-18 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(6,-18)) := by
  refine ⟨44, w6_n18_pattern, 0, 0, w6_n18_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_n18_pattern q l 0 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨0, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w6_n18_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 0 0
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w6_n18_counts_eq]
    exact w6_n18_support

def w6_n16_counts : DeltaLOneSignedInput.Species → Nat := ![0,0,14,0,0,0,8,0,12,4]
def w6_n16_pattern (i : Fin 38) : DeltaLOneSignedInput.Species := if i.val < 14 then 2 else if i.val < 22 then 6 else if i.val < 34 then 8 else if i.val < 38 then 9 else 0
theorem w6_n16_counts_eq : SMIteratedContent.counts w6_n16_pattern = w6_n16_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w6_n16_support : SMJointContentSupport.Supports w6_n16_counts 0 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w6_n16_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w6_n16_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w6_n16_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  refine ⟨38, w6_n16_pattern, 0, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_n16_pattern q l 0 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨0, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 0 0; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w6_n16_counts_eq]
  exact w6_n16_support

theorem w6_n16_charges : SMQLPatternRequests.blCharge w6_n16_pattern = (6,-16) := by
  decide +kernel

theorem w6_n16_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (-16 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  apply w6_n16_allowed
  rw [SMChargeDegreeBounds.residual_linear, w6_n16_charges]
  simpa using hc

theorem w6_n16_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (-16 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(6,-16)) := by
  refine ⟨38, w6_n16_pattern, 0, 0, w6_n16_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_n16_pattern q l 0 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨0, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w6_n16_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 0 0
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w6_n16_counts_eq]
    exact w6_n16_support

def w6_n14_counts : DeltaLOneSignedInput.Species → Nat := ![0,0,12,0,0,0,6,0,12,2]
def w6_n14_pattern (i : Fin 32) : DeltaLOneSignedInput.Species := if i.val < 12 then 2 else if i.val < 18 then 6 else if i.val < 30 then 8 else if i.val < 32 then 9 else 0
theorem w6_n14_counts_eq : SMIteratedContent.counts w6_n14_pattern = w6_n14_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w6_n14_support : SMJointContentSupport.Supports w6_n14_counts 0 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w6_n14_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w6_n14_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w6_n14_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  refine ⟨32, w6_n14_pattern, 0, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_n14_pattern q l 0 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨0, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 0 0; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w6_n14_counts_eq]
  exact w6_n14_support

theorem w6_n14_charges : SMQLPatternRequests.blCharge w6_n14_pattern = (6,-14) := by
  decide +kernel

theorem w6_n14_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (-14 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  apply w6_n14_allowed
  rw [SMChargeDegreeBounds.residual_linear, w6_n14_charges]
  simpa using hc

theorem w6_n14_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (-14 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(6,-14)) := by
  refine ⟨32, w6_n14_pattern, 0, 0, w6_n14_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_n14_pattern q l 0 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨0, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w6_n14_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 0 0
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w6_n14_counts_eq]
    exact w6_n14_support

def w6_n12_counts : DeltaLOneSignedInput.Species → Nat := ![0,0,10,0,0,0,4,0,12,0]
def w6_n12_pattern (i : Fin 26) : DeltaLOneSignedInput.Species := if i.val < 10 then 2 else if i.val < 14 then 6 else if i.val < 26 then 8 else 0
theorem w6_n12_counts_eq : SMIteratedContent.counts w6_n12_pattern = w6_n12_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w6_n12_support : SMJointContentSupport.Supports w6_n12_counts 0 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w6_n12_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w6_n12_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w6_n12_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  refine ⟨26, w6_n12_pattern, 0, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_n12_pattern q l 0 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨0, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 0 0; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w6_n12_counts_eq]
  exact w6_n12_support

theorem w6_n12_charges : SMQLPatternRequests.blCharge w6_n12_pattern = (6,-12) := by
  decide +kernel

theorem w6_n12_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (-12 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  apply w6_n12_allowed
  rw [SMChargeDegreeBounds.residual_linear, w6_n12_charges]
  simpa using hc

theorem w6_n12_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (-12 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(6,-12)) := by
  refine ⟨26, w6_n12_pattern, 0, 0, w6_n12_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_n12_pattern q l 0 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨0, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w6_n12_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 0 0
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w6_n12_counts_eq]
    exact w6_n12_support

def w6_n10_counts : DeltaLOneSignedInput.Species → Nat := ![0,2,8,0,0,0,4,0,10,0]
def w6_n10_pattern (i : Fin 24) : DeltaLOneSignedInput.Species := if i.val < 2 then 1 else if i.val < 10 then 2 else if i.val < 14 then 6 else if i.val < 24 then 8 else 0
theorem w6_n10_counts_eq : SMIteratedContent.counts w6_n10_pattern = w6_n10_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w6_n10_support : SMJointContentSupport.Supports w6_n10_counts 2 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w6_n10_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w6_n10_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w6_n10_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  refine ⟨24, w6_n10_pattern, 0, 2, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_n10_pattern q l 0 2).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨2, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 2 2; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w6_n10_counts_eq]
  exact w6_n10_support

theorem w6_n10_charges : SMQLPatternRequests.blCharge w6_n10_pattern = (6,-10) := by
  decide +kernel

theorem w6_n10_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (-10 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  apply w6_n10_allowed
  rw [SMChargeDegreeBounds.residual_linear, w6_n10_charges]
  simpa using hc

theorem w6_n10_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (-10 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(6,-10)) := by
  refine ⟨24, w6_n10_pattern, 0, 2, w6_n10_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_n10_pattern q l 0 2).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨2, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w6_n10_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 2 2
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w6_n10_counts_eq]
    exact w6_n10_support

def w6_n8_counts : DeltaLOneSignedInput.Species → Nat := ![0,2,8,0,0,0,4,0,8,0]
def w6_n8_pattern (i : Fin 22) : DeltaLOneSignedInput.Species := if i.val < 2 then 1 else if i.val < 10 then 2 else if i.val < 14 then 6 else if i.val < 22 then 8 else 0
theorem w6_n8_counts_eq : SMIteratedContent.counts w6_n8_pattern = w6_n8_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w6_n8_support : SMJointContentSupport.Supports w6_n8_counts 0 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w6_n8_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w6_n8_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w6_n8_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  refine ⟨22, w6_n8_pattern, 0, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_n8_pattern q l 0 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨0, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 0 0; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w6_n8_counts_eq]
  exact w6_n8_support

theorem w6_n8_charges : SMQLPatternRequests.blCharge w6_n8_pattern = (6,-8) := by
  decide +kernel

theorem w6_n8_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (-8 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  apply w6_n8_allowed
  rw [SMChargeDegreeBounds.residual_linear, w6_n8_charges]
  simpa using hc

theorem w6_n8_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (-8 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(6,-8)) := by
  refine ⟨22, w6_n8_pattern, 0, 0, w6_n8_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_n8_pattern q l 0 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨0, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w6_n8_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 0 0
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w6_n8_counts_eq]
    exact w6_n8_support

def w6_n6_counts : DeltaLOneSignedInput.Species → Nat := ![0,2,6,0,0,0,2,0,6,0]
def w6_n6_pattern (i : Fin 16) : DeltaLOneSignedInput.Species := if i.val < 2 then 1 else if i.val < 8 then 2 else if i.val < 10 then 6 else if i.val < 16 then 8 else 0
theorem w6_n6_counts_eq : SMIteratedContent.counts w6_n6_pattern = w6_n6_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w6_n6_support : SMJointContentSupport.Supports w6_n6_counts 2 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w6_n6_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w6_n6_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w6_n6_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  refine ⟨16, w6_n6_pattern, 0, 2, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_n6_pattern q l 0 2).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨2, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 2 2; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w6_n6_counts_eq]
  exact w6_n6_support

theorem w6_n6_charges : SMQLPatternRequests.blCharge w6_n6_pattern = (6,-6) := by
  decide +kernel

theorem w6_n6_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (-6 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  apply w6_n6_allowed
  rw [SMChargeDegreeBounds.residual_linear, w6_n6_charges]
  simpa using hc

theorem w6_n6_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (-6 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(6,-6)) := by
  refine ⟨16, w6_n6_pattern, 0, 2, w6_n6_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_n6_pattern q l 0 2).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨2, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w6_n6_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 2 2
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w6_n6_counts_eq]
    exact w6_n6_support

def w6_n4_counts : DeltaLOneSignedInput.Species → Nat := ![0,2,6,0,0,0,2,0,4,0]
def w6_n4_pattern (i : Fin 14) : DeltaLOneSignedInput.Species := if i.val < 2 then 1 else if i.val < 8 then 2 else if i.val < 10 then 6 else if i.val < 14 then 8 else 0
theorem w6_n4_counts_eq : SMIteratedContent.counts w6_n4_pattern = w6_n4_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w6_n4_support : SMJointContentSupport.Supports w6_n4_counts 0 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w6_n4_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w6_n4_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w6_n4_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  refine ⟨14, w6_n4_pattern, 0, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_n4_pattern q l 0 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨0, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 0 0; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w6_n4_counts_eq]
  exact w6_n4_support

theorem w6_n4_charges : SMQLPatternRequests.blCharge w6_n4_pattern = (6,-4) := by
  decide +kernel

theorem w6_n4_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (-4 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  apply w6_n4_allowed
  rw [SMChargeDegreeBounds.residual_linear, w6_n4_charges]
  simpa using hc

theorem w6_n4_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (-4 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(6,-4)) := by
  refine ⟨14, w6_n4_pattern, 0, 0, w6_n4_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_n4_pattern q l 0 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨0, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w6_n4_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 0 0
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w6_n4_counts_eq]
    exact w6_n4_support

def w6_n2_counts : DeltaLOneSignedInput.Species → Nat := ![0,2,4,0,0,0,0,0,2,0]
def w6_n2_pattern (i : Fin 8) : DeltaLOneSignedInput.Species := if i.val < 2 then 1 else if i.val < 6 then 2 else if i.val < 8 then 8 else 0
theorem w6_n2_counts_eq : SMIteratedContent.counts w6_n2_pattern = w6_n2_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w6_n2_support : SMJointContentSupport.Supports w6_n2_counts 2 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w6_n2_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w6_n2_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w6_n2_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  refine ⟨8, w6_n2_pattern, 0, 2, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_n2_pattern q l 0 2).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨2, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 2 2; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w6_n2_counts_eq]
  exact w6_n2_support

theorem w6_n2_charges : SMQLPatternRequests.blCharge w6_n2_pattern = (6,-2) := by
  decide +kernel

theorem w6_n2_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (-2 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  apply w6_n2_allowed
  rw [SMChargeDegreeBounds.residual_linear, w6_n2_charges]
  simpa using hc

theorem w6_n2_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (-2 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(6,-2)) := by
  refine ⟨8, w6_n2_pattern, 0, 2, w6_n2_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_n2_pattern q l 0 2).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨2, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w6_n2_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 2 2
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w6_n2_counts_eq]
    exact w6_n2_support

def w6_p0_counts : DeltaLOneSignedInput.Species → Nat := ![6,0,0,0,0,0,0,0,0,0]
def w6_p0_pattern (i : Fin 6) : DeltaLOneSignedInput.Species := if i.val < 6 then 0 else 0
theorem w6_p0_counts_eq : SMIteratedContent.counts w6_p0_pattern = w6_p0_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w6_p0_support : SMJointContentSupport.Supports w6_p0_counts 2 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w6_p0_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w6_p0_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w6_p0_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  refine ⟨6, w6_p0_pattern, 0, 2, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_p0_pattern q l 0 2).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨2, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 2 2; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w6_p0_counts_eq]
  exact w6_p0_support

theorem w6_p0_charges : SMQLPatternRequests.blCharge w6_p0_pattern = (6,0) := by
  decide +kernel

theorem w6_p0_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (0 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  apply w6_p0_allowed
  rw [SMChargeDegreeBounds.residual_linear, w6_p0_charges]
  simpa using hc

theorem w6_p0_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (0 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(6,0)) := by
  refine ⟨6, w6_p0_pattern, 0, 2, w6_p0_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_p0_pattern q l 0 2).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨2, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w6_p0_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 2 2
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w6_p0_counts_eq]
    exact w6_p0_support

def w6_p2_counts : DeltaLOneSignedInput.Species → Nat := ![6,0,0,2,0,0,0,0,0,0]
def w6_p2_pattern (i : Fin 8) : DeltaLOneSignedInput.Species := if i.val < 6 then 0 else if i.val < 8 then 3 else 0
theorem w6_p2_counts_eq : SMIteratedContent.counts w6_p2_pattern = w6_p2_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w6_p2_support : SMJointContentSupport.Supports w6_p2_counts 0 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w6_p2_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w6_p2_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w6_p2_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  refine ⟨8, w6_p2_pattern, 0, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_p2_pattern q l 0 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨0, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 0 0; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w6_p2_counts_eq]
  exact w6_p2_support

theorem w6_p2_charges : SMQLPatternRequests.blCharge w6_p2_pattern = (6,2) := by
  decide +kernel

theorem w6_p2_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (2 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  apply w6_p2_allowed
  rw [SMChargeDegreeBounds.residual_linear, w6_p2_charges]
  simpa using hc

theorem w6_p2_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (2 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(6,2)) := by
  refine ⟨8, w6_p2_pattern, 0, 0, w6_p2_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_p2_pattern q l 0 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨0, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w6_p2_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 0 0
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w6_p2_counts_eq]
    exact w6_p2_support

def w6_p4_counts : DeltaLOneSignedInput.Species → Nat := ![6,0,0,4,0,0,0,0,0,0]
def w6_p4_pattern (i : Fin 10) : DeltaLOneSignedInput.Species := if i.val < 6 then 0 else if i.val < 10 then 3 else 0
theorem w6_p4_counts_eq : SMIteratedContent.counts w6_p4_pattern = w6_p4_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w6_p4_support : SMJointContentSupport.Supports w6_p4_counts 2 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w6_p4_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w6_p4_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w6_p4_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  refine ⟨10, w6_p4_pattern, 2, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_p4_pattern q l 2 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨2, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 2 0 2; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w6_p4_counts_eq]
  exact w6_p4_support

theorem w6_p4_charges : SMQLPatternRequests.blCharge w6_p4_pattern = (6,4) := by
  decide +kernel

theorem w6_p4_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (4 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  apply w6_p4_allowed
  rw [SMChargeDegreeBounds.residual_linear, w6_p4_charges]
  simpa using hc

theorem w6_p4_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (4 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(6,4)) := by
  refine ⟨10, w6_p4_pattern, 2, 0, w6_p4_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_p4_pattern q l 2 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨2, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w6_p4_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 2 0 2
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w6_p4_counts_eq]
    exact w6_p4_support

def w6_p6_counts : DeltaLOneSignedInput.Species → Nat := ![6,2,0,6,0,0,0,2,0,0]
def w6_p6_pattern (i : Fin 16) : DeltaLOneSignedInput.Species := if i.val < 6 then 0 else if i.val < 8 then 1 else if i.val < 14 then 3 else if i.val < 16 then 7 else 0
theorem w6_p6_counts_eq : SMIteratedContent.counts w6_p6_pattern = w6_p6_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w6_p6_support : SMJointContentSupport.Supports w6_p6_counts 0 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w6_p6_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w6_p6_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w6_p6_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  refine ⟨16, w6_p6_pattern, 0, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_p6_pattern q l 0 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨0, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 0 0; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w6_p6_counts_eq]
  exact w6_p6_support

theorem w6_p6_charges : SMQLPatternRequests.blCharge w6_p6_pattern = (6,6) := by
  decide +kernel

theorem w6_p6_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (6 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  apply w6_p6_allowed
  rw [SMChargeDegreeBounds.residual_linear, w6_p6_charges]
  simpa using hc

theorem w6_p6_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (6 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(6,6)) := by
  refine ⟨16, w6_p6_pattern, 0, 0, w6_p6_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_p6_pattern q l 0 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨0, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w6_p6_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 0 0
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w6_p6_counts_eq]
    exact w6_p6_support

def w6_p8_counts : DeltaLOneSignedInput.Species → Nat := ![6,2,0,8,0,0,0,2,0,0]
def w6_p8_pattern (i : Fin 18) : DeltaLOneSignedInput.Species := if i.val < 6 then 0 else if i.val < 8 then 1 else if i.val < 16 then 3 else if i.val < 18 then 7 else 0
theorem w6_p8_counts_eq : SMIteratedContent.counts w6_p8_pattern = w6_p8_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w6_p8_support : SMJointContentSupport.Supports w6_p8_counts 2 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w6_p8_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w6_p8_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w6_p8_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  refine ⟨18, w6_p8_pattern, 2, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_p8_pattern q l 2 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨2, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 2 0 2; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w6_p8_counts_eq]
  exact w6_p8_support

theorem w6_p8_charges : SMQLPatternRequests.blCharge w6_p8_pattern = (6,8) := by
  decide +kernel

theorem w6_p8_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (8 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  apply w6_p8_allowed
  rw [SMChargeDegreeBounds.residual_linear, w6_p8_charges]
  simpa using hc

theorem w6_p8_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (8 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(6,8)) := by
  refine ⟨18, w6_p8_pattern, 2, 0, w6_p8_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_p8_pattern q l 2 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨2, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w6_p8_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 2 0 2
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w6_p8_counts_eq]
    exact w6_p8_support

def w6_p10_counts : DeltaLOneSignedInput.Species → Nat := ![6,4,0,10,0,0,0,4,0,0]
def w6_p10_pattern (i : Fin 24) : DeltaLOneSignedInput.Species := if i.val < 6 then 0 else if i.val < 10 then 1 else if i.val < 20 then 3 else if i.val < 24 then 7 else 0
theorem w6_p10_counts_eq : SMIteratedContent.counts w6_p10_pattern = w6_p10_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w6_p10_support : SMJointContentSupport.Supports w6_p10_counts 0 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w6_p10_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w6_p10_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w6_p10_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  refine ⟨24, w6_p10_pattern, 0, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_p10_pattern q l 0 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨0, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 0 0; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w6_p10_counts_eq]
  exact w6_p10_support

theorem w6_p10_charges : SMQLPatternRequests.blCharge w6_p10_pattern = (6,10) := by
  decide +kernel

theorem w6_p10_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (10 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  apply w6_p10_allowed
  rw [SMChargeDegreeBounds.residual_linear, w6_p10_charges]
  simpa using hc

theorem w6_p10_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (10 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(6,10)) := by
  refine ⟨24, w6_p10_pattern, 0, 0, w6_p10_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_p10_pattern q l 0 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨0, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w6_p10_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 0 0
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w6_p10_counts_eq]
    exact w6_p10_support

def w6_p12_counts : DeltaLOneSignedInput.Species → Nat := ![0,8,0,12,0,0,0,2,0,0]
def w6_p12_pattern (i : Fin 22) : DeltaLOneSignedInput.Species := if i.val < 8 then 1 else if i.val < 20 then 3 else if i.val < 22 then 7 else 0
theorem w6_p12_counts_eq : SMIteratedContent.counts w6_p12_pattern = w6_p12_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w6_p12_support : SMJointContentSupport.Supports w6_p12_counts 0 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w6_p12_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w6_p12_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w6_p12_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  refine ⟨22, w6_p12_pattern, 0, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_p12_pattern q l 0 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨0, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 0 0; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w6_p12_counts_eq]
  exact w6_p12_support

theorem w6_p12_charges : SMQLPatternRequests.blCharge w6_p12_pattern = (6,12) := by
  decide +kernel

theorem w6_p12_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (12 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  apply w6_p12_allowed
  rw [SMChargeDegreeBounds.residual_linear, w6_p12_charges]
  simpa using hc

theorem w6_p12_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (12 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(6,12)) := by
  refine ⟨22, w6_p12_pattern, 0, 0, w6_p12_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_p12_pattern q l 0 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨0, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w6_p12_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 0 0
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w6_p12_counts_eq]
    exact w6_p12_support

def w6_p14_counts : DeltaLOneSignedInput.Species → Nat := ![0,10,0,12,2,0,0,4,0,0]
def w6_p14_pattern (i : Fin 28) : DeltaLOneSignedInput.Species := if i.val < 10 then 1 else if i.val < 22 then 3 else if i.val < 24 then 4 else if i.val < 28 then 7 else 0
theorem w6_p14_counts_eq : SMIteratedContent.counts w6_p14_pattern = w6_p14_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w6_p14_support : SMJointContentSupport.Supports w6_p14_counts 0 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w6_p14_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w6_p14_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w6_p14_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  refine ⟨28, w6_p14_pattern, 0, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_p14_pattern q l 0 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨0, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 0 0; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w6_p14_counts_eq]
  exact w6_p14_support

theorem w6_p14_charges : SMQLPatternRequests.blCharge w6_p14_pattern = (6,14) := by
  decide +kernel

theorem w6_p14_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (14 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  apply w6_p14_allowed
  rw [SMChargeDegreeBounds.residual_linear, w6_p14_charges]
  simpa using hc

theorem w6_p14_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (14 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(6,14)) := by
  refine ⟨28, w6_p14_pattern, 0, 0, w6_p14_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_p14_pattern q l 0 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨0, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w6_p14_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 0 0
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w6_p14_counts_eq]
    exact w6_p14_support

def w6_p16_counts : DeltaLOneSignedInput.Species → Nat := ![0,12,0,12,4,0,0,6,0,0]
def w6_p16_pattern (i : Fin 34) : DeltaLOneSignedInput.Species := if i.val < 12 then 1 else if i.val < 24 then 3 else if i.val < 28 then 4 else if i.val < 34 then 7 else 0
theorem w6_p16_counts_eq : SMIteratedContent.counts w6_p16_pattern = w6_p16_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w6_p16_support : SMJointContentSupport.Supports w6_p16_counts 0 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w6_p16_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w6_p16_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w6_p16_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  refine ⟨34, w6_p16_pattern, 0, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_p16_pattern q l 0 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨0, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 0 0; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w6_p16_counts_eq]
  exact w6_p16_support

theorem w6_p16_charges : SMQLPatternRequests.blCharge w6_p16_pattern = (6,16) := by
  decide +kernel

theorem w6_p16_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (16 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  apply w6_p16_allowed
  rw [SMChargeDegreeBounds.residual_linear, w6_p16_charges]
  simpa using hc

theorem w6_p16_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (16 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(6,16)) := by
  refine ⟨34, w6_p16_pattern, 0, 0, w6_p16_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_p16_pattern q l 0 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨0, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w6_p16_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 0 0
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w6_p16_counts_eq]
    exact w6_p16_support

def w6_p18_counts : DeltaLOneSignedInput.Species → Nat := ![0,14,0,12,6,0,0,8,0,0]
def w6_p18_pattern (i : Fin 40) : DeltaLOneSignedInput.Species := if i.val < 14 then 1 else if i.val < 26 then 3 else if i.val < 32 then 4 else if i.val < 40 then 7 else 0
theorem w6_p18_counts_eq : SMIteratedContent.counts w6_p18_pattern = w6_p18_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem w6_p18_support : SMJointContentSupport.Supports w6_p18_counts 0 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced w6_p18_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem w6_p18_allowed {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l w6_p18_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  refine ⟨40, w6_p18_pattern, 0, 0, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_p18_pattern q l 0 0).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨0, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible 0 0 0; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [w6_p18_counts_eq]
  exact w6_p18_support

theorem w6_p18_charges : SMQLPatternRequests.blCharge w6_p18_pattern = (6,18) := by
  decide +kernel

theorem w6_p18_neutral {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (18 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) := by
  apply w6_p18_allowed
  rw [SMChargeDegreeBounds.residual_linear, w6_p18_charges]
  simpa using hc

theorem w6_p18_exact {k : Nat} [NeZero k] (q l : ZMod k)
    (hc : (6 : ZMod k)*q + (18 : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=(6,18)) := by
  refine ⟨40, w6_p18_pattern, 0, 0, w6_p18_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff w6_p18_pattern q l 0 0).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨0, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, w6_p18_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 0 0
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [w6_p18_counts_eq]
    exact w6_p18_support

end GUT.SMLeptonChargeWitnesses
