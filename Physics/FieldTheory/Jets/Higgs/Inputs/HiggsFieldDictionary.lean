import Math.RepresentationTheory.Constructions.PairedComponentFields
import Physics.StandardModel.Gauge.Tensors.SMGaugeConjugation

/-! Actual Higgs/dual component labels on the covering SM gauge group.
This is a field dictionary, independent of a full jet invariant-basis claim. -/
namespace Physics.HiggsFieldDictionary
set_option autoImplicit false
noncomputable section
open Math Representation StandardSMGaugeTensor

abbrev Labels := Bool × Fin 2
abbrev Fields := JetLinear.Field Labels
abbrev V := Fin 2 → ℂ
def higgs := twist weak 3
def action := PairedComponentFields.action higgs

def components : Fields ≃ₗ[ℂ] V × V :=
  PairedComponentFields.fieldEquiv.trans
    ((LinearEquiv.refl ℂ V).prodCongr SMGaugeConjugation.higgsDual.toLinearEquiv)

theorem components_apply (p : Fields) :
    components p = (fun i => p (false,i),fun i => p (true,i)) := by
  apply Prod.ext
  · rfl
  · funext i
    change SpecialUnitaryContragredient.coordinates 2
      (PairedComponentFields.dualCoordinates (fun k => p (true,k))) i = _
    rw [SpecialUnitaryContragredient.coordinates_apply]
    fin_cases i <;> simp [PairedComponentFields.dualCoordinates]

theorem components_action (g : GaugeGroup) (p : Fields) :
    components (action g p) =
      (higgs g (components p).1,higgs (SMGaugeConjugation.conjugate g) (components p).2) := by
  change ((PairedComponentFields.fieldEquiv (action g p)).1,
    SMGaugeConjugation.higgsDual (PairedComponentFields.fieldEquiv (action g p)).2) = _
  unfold action
  rw [PairedComponentFields.fieldEquiv_action]
  apply Prod.ext
  · rfl
  · exact SMGaugeConjugation.higgsDual.toIntertwiningMap.isIntertwining _ _ g _

def pairing (p : Fields) : ℂ := PairedComponentFields.contraction p

theorem pairing_coordinates (p : Fields) :
    pairing p = ∑ i : Fin 2, p (true,i)*p (false,i) := rfl

theorem pairing_invariant (g : GaugeGroup) (p : Fields) :
    pairing (action g p) = pairing p :=
  PairedComponentFields.contraction_invariant higgs g p

/-- Physical conjugate values are a real-form condition, not a complex-linear identification. -/
def ConjugateValues (p : Fields) : Prop := ∀ i, p (true,i) = star (p (false,i))

theorem conjugate_action (g : GaugeGroup) (v : V) :
    star (higgs g v) = higgs (SMGaugeConjugation.conjugate g) (star v) := by
  have hp : phase 3 (SMGaugeConjugation.conjugate g) = star (phase 3 g) := by
    calc
      _ = ((g.2.2⁻¹ : Circle) : ℂ) ^ (3:ℤ) := rfl
      _ = (star (g.2.2 : ℂ)) ^ (3:ℤ) :=
        congrArg (fun z : ℂ => z ^ (3:ℤ)) (Circle.coe_inv_eq_conj g.2.2)
      _ = star ((g.2.2 : ℂ) ^ (3:ℤ)) := (star_zpow₀ _ _).symm
      _ = _ := rfl
  funext i
  change star (phase 3 g * ((g.2.1 : Matrix (Fin 2) (Fin 2) ℂ).mulVec v) i) =
    phase 3 (SMGaugeConjugation.conjugate g) *
      (((g.2.1 : Matrix (Fin 2) (Fin 2) ℂ).map star).mulVec (star v)) i
  rw [hp]
  simp [Matrix.mulVec,dotProduct]

theorem conjugateValues_stable (g : GaugeGroup) (p : Fields) (hp : ConjugateValues p) :
    ConjugateValues (action g p) := by
  have he := components_action g p
  rw [components_apply,components_apply] at he
  have hf := congrArg Prod.fst he
  have hb := congrArg Prod.snd he
  have hv : (fun i => p (true,i)) = star (fun i => p (false,i)) := funext hp
  change (fun i => action g p (false,i)) = higgs g (fun i => p (false,i)) at hf
  change (fun i => action g p (true,i)) =
    higgs (SMGaugeConjugation.conjugate g) (fun i => p (true,i)) at hb
  rw [hv,← conjugate_action] at hb
  intro i
  exact (congrFun hb i).trans (congrArg star (congrFun hf i)).symm

theorem pairing_conjugate (p : Fields) (hp : ConjugateValues p) :
    pairing p = ∑ i : Fin 2, star (p (false,i))*p (false,i) := by
  rw [pairing_coordinates]
  apply Finset.sum_congr rfl
  intro i _
  rw [hp i]

end
end Physics.HiggsFieldDictionary
