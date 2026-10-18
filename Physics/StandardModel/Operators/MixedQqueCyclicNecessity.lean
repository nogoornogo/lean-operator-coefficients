import Physics.StandardModel.Operators.FlavoredCyclicSelection

/-! Mixed Q pairs give necessary input constraints on the actual flavored
exterior sector. The controls certify extra coverage over diagonal pairs,
not a SU(6) realization or a new independent coefficient dictionary. -/
namespace GUT.MixedQqueCyclicNecessity
set_option autoImplicit false
noncomputable section
open Math Representation CyclicWeightCoordinates FlavoredCyclicCoordinates SelectionCriteria
variable {N : ℕ} [NeZero N]
  {I J K : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

omit [NeZero N] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K] in
theorem pair_charge (q : I → ZMod N) (u : J → ZMod N) (e : K → ZMod N)
    (i j : I) (a : J) (b : K) :
    qqueCharge q u e (TauCeti.Sym.ofFn ![i,j], (a,b)) =
      q i + q j + (u a + e b) := by
  simp only [qqueCharge, symmetricCharge_pair]

theorem neutral_pair_allowed (q : I → ZMod N) (u : J → ZMod N) (e : K → ZMod N)
    (i j : I) (a : J) (b : K) (h : q i + q j + (u a + e b) = 0) :
    Allowed (QquePhysicalExteriorCompleteness.Sector (diagonal q) (diagonal u) (diagonal e)) := by
  apply (qque_allowed q u e).mpr
  exact ⟨(TauCeti.Sym.ofFn ![i,j], (a,b)), (pair_charge q u e i j a b).trans h⟩

theorem necessary (q : I → ZMod N) (u : J → ZMod N) (e : K → ZMod N)
    (hp : Forbidden (QquePhysicalExteriorCompleteness.Sector
      (diagonal q) (diagonal u) (diagonal e))) (i j : I) (a : J) (b : K) :
    q i + q j + (u a + e b) ≠ 0 := by
  intro h
  exact ((forbidden_iff_not_allowed _).mp hp) (neutral_pair_allowed q u e i j a b h)

theorem total_necessary
    (S : Fin 5 → Type) [∀ s, Fintype (S s)] [∀ s, DecidableEq (S s)]
    (c : ∀ s, S s → ZMod N)
    (hp : Forbidden (DeltaLOneSignedFields.Sector (FlavoredCyclicSelection.flavor S c) 1))
    (i j : S 0) (a : S 1) (b : S 4) :
    c 0 i + c 0 j + (c 1 a + c 4 b) ≠ 0 := by
  intro h
  have hi := ((FlavoredCyclicSelection.forbidden_total_iff S c).mp hp).2.1
  exact hi.false ⟨(TauCeti.Sym.ofFn ![i,j], (a,b)),
    (pair_charge (c 0) (c 1) (c 4) i j a b).trans h⟩

/-- Three actual generation coordinates with two distinct cyclic weights. -/
def controlQ (i : Fin 3) : ZMod 3 := if i = 1 then 1 else 0
def controlU (_ : Fin 3) : ZMod 3 := 0
def controlE (_ : Fin 3) : ZMod 3 := 2

theorem control_diagonal_passes (i a b : Fin 3) :
    controlQ i + controlQ i + (controlU a + controlE b) ≠ 0 := by
  simp only [controlU, controlE]
  fin_cases i <;> decide +kernel

theorem control_mixed_neutral :
    controlQ 0 + controlQ 1 + (controlU 0 + controlE 0) = 0 := by
  decide +kernel

theorem control_allowed :
    Allowed (QquePhysicalExteriorCompleteness.Sector
      (diagonal controlQ) (diagonal controlU) (diagonal controlE)) :=
  neutral_pair_allowed controlQ controlU controlE 0 1 0 0 control_mixed_neutral

theorem control_not_forbidden :
    ¬ Forbidden (QquePhysicalExteriorCompleteness.Sector
      (diagonal controlQ) (diagonal controlU) (diagonal controlE)) := by
  rw [forbidden_iff_not_allowed]
  exact not_not.mpr control_allowed

/-- A full signed three-generation input; no Yukawa or UV claim is attached. -/
def controlCharges (s : Fin 5) : Fin 3 → ZMod 3 :=
  ![controlQ, controlU, controlU, controlU, controlE] s

theorem control_total_allowed :
    Allowed (DeltaLOneSignedFields.Sector
      (FlavoredCyclicSelection.flavor (fun _ => Fin 3) controlCharges) 1) := by
  apply (FlavoredCyclicSelection.allowed_total_iff (fun _ => Fin 3) controlCharges).mpr
  apply Or.inr
  apply Or.inl
  refine ⟨⟨(TauCeti.Sym.ofFn ![(0 : Fin 3),1], ((0 : Fin 3),0)), ?_⟩⟩
  rw [pair_charge]
  change controlQ 0 + controlQ 1 + (controlU 0 + controlE 0) = 0
  exact control_mixed_neutral

end
end GUT.MixedQqueCyclicNecessity
