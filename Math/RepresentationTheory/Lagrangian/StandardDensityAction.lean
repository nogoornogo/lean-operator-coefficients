import Math.Algebra.Jets.BlockJetSubstitution
import Math.Algebra.Jets.JetCombined
import Math.RepresentationTheory.Lagrangian.DensitySymmetry
import Mathlib.LinearAlgebra.Finsupp.SumProd

/-! The standard mixed global action automatically supplies all action-side
Euler-naturality obligations. Callers supply representations and density invariance. -/
namespace Math.StandardDensityAction
set_option autoImplicit false
noncomputable section
open LocalPolynomial LocalPolynomial.BlockJetSubstitution JetLinear JetDirections
variable {F B I H : Type*} [Group H] [Fintype I]
variable (rF : Representation ℂ H (JetLinear.Field F))
  (rB : Representation ℂ H (JetLinear.Field B))
  (rI : Representation ℂ H (Direction I))

/-- Separate field species are preserved by the action. -/
def split : (LocalPolynomial.Field F B →₀ ℂ) ≃ₗ[ℂ]
    JetLinear.Field F × JetLinear.Field B := Finsupp.sumFinsuppLEquivProdFinsupp ℂ

def fieldAction : Representation ℂ H (LocalPolynomial.Field F B →₀ ℂ) :=
  (split (F := F) (B := B)).symm.conjRingEquiv.toMonoidHom.comp (rF.prod rB)

def fieldEquiv (g : H) : (LocalPolynomial.Field F B →₀ ℂ) ≃ₗ[ℂ]
    (LocalPolynomial.Field F B →₀ ℂ) :=
  LinearEquiv.ofLinearMap (fieldAction rF rB g) (fieldAction rF rB g⁻¹)
    (by apply LinearMap.ext; intro v; exact Representation.self_inv_apply (fieldAction rF rB) g v)
    (by apply LinearMap.ext; intro v; exact Representation.inv_self_apply (fieldAction rF rB) g v)

omit [Fintype I] in
theorem oddIn_shift (i : I) (v : Jet F I) :
    oddIn (B := B) (JetLinear.shift i v) = JetLinear.shift i (oddIn v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add,hv,hw]
  | single j c => simp [ScalarJetAlgebra.shift]
omit [Fintype I] in
theorem evenIn_shift (i : I) (v : Jet B I) :
    evenIn (F := F) (JetLinear.shift i v) = JetLinear.shift i (evenIn v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add,hv,hw]
  | single j c => simp [ScalarJetAlgebra.shift]

omit [Fintype I] in
@[simp] theorem oddIn_atOrder (a : I →₀ ℕ) (v : JetLinear.Field F) :
    oddIn (B := B) (atOrder a v) = atOrder a (Finsupp.sumElim v (0 : B →₀ ℂ)) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw =>
    simp only [map_add,hv,hw]
    rw [← map_add]
    congr 1
    simpa only [zero_add] using (Finsupp.sumElim_add v w (0 : B →₀ ℂ) 0).symm
  | single f c => simp

omit [Fintype I] in
@[simp] theorem evenIn_atOrder (a : I →₀ ℕ) (v : JetLinear.Field B) :
    evenIn (F := F) (atOrder a v) = atOrder a (Finsupp.sumElim (0 : F →₀ ℂ) v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw =>
    simp only [map_add,hv,hw]
    rw [← map_add]
    congr 1
    simpa only [zero_add] using (Finsupp.sumElim_add (0 : F →₀ ℂ) 0 v w).symm
  | single b c => simp

@[simp] theorem fieldAction_odd (f : F) (c : ℂ) (g : H) :
    fieldAction rF rB g (Finsupp.single (.inl f) c) =
      Finsupp.sumElim (rF g (Finsupp.single f c)) 0 := by
  classical
  simp [fieldAction,split,Finsupp.sumFinsuppLEquivProdFinsupp]

@[simp] theorem fieldAction_even (b : B) (c : ℂ) (g : H) :
    fieldAction rF rB g (Finsupp.single (.inr b) c) =
      Finsupp.sumElim 0 (rB g (Finsupp.single b c)) := by
  classical
  simp [fieldAction,split,Finsupp.sumFinsuppLEquivProdFinsupp]

/-- Canonical action-side certificate for arbitrary component and direction representations. -/
def prolongation (g : H) : Prolongation F B I where
  toLinearSubstitution := substitution (combined rF rI g) (combined rB rI g)
  fields := fieldAction rF rB g
  directions i j := (rI g (Finsupp.single i 1)) j
  base_map := by
    intro v
    change jets (combined rF rI g) (combined rB rI g) (atOrder 0 v) = _
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp only [map_add,hv,hw]
    | single s c =>
      have hs : Finsupp.single s c = c • Finsupp.single s (1:ℂ) := by simp
      rw [hs,map_smul,map_smul,map_smul,map_smul]
      congr 1
      cases s with
      | inl f =>
        rw [atOrder_single,jets_odd,← atOrder_single 0 f 1,combined_zero,oddIn_atOrder,
          fieldAction_odd]
      | inr b =>
        rw [atOrder_single,jets_even,← atOrder_single 0 b 1,combined_zero,evenIn_atOrder,
          fieldAction_even]
  shift_map := by
    intro i v
    change jets (combined rF rI g) (combined rB rI g) (JetLinear.shift i v) = _
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp only [map_add,hv,hw,smul_add,Finset.sum_add_distrib]
    | single j c =>
      obtain ⟨s,a⟩ := j
      have hs : Finsupp.single (s,a) c = c • Finsupp.single (s,a) (1:ℂ) := by simp
      rw [hs,map_smul,map_smul]
      simp only [map_smul,← smul_comm c,← Finset.smul_sum]
      congr 1
      cases s with
      | inl f =>
        simp only [JetLinear.shift_single,ScalarJetAlgebra.shift,jets_odd]
        have hc := combined_covariant rF rI g i (Finsupp.single (f,a) 1)
        simp only [JetLinear.shift_single,ScalarJetAlgebra.shift] at hc
        rw [hc,map_sum]
        simp only [substitution,jets_odd,map_smul,oddIn_shift]
      | inr b =>
        simp only [JetLinear.shift_single,ScalarJetAlgebra.shift,jets_even]
        have hc := combined_covariant rB rI g i (Finsupp.single (b,a) 1)
        simp only [JetLinear.shift_single,ScalarJetAlgebra.shift] at hc
        rw [hc,map_sum]
        simp only [substitution,jets_even,map_smul,evenIn_shift]
  derivative_map := by
    intro i a
    exact JetFunctor.mixed_covariant (combined rF rI) (combined rB rI) g i _
      (fun v => combined_covariant rF rI g i v)
      (fun v => combined_covariant rB rI g i v) a

def action := JetFunctor.mixedAction (combined rF rI) (combined rB rI)

def model (p : Expr F B I) (hp : ∀ g, action rF rB rI g p.eval = p.eval) :
    LagrangianModel.Mixed F B I H :=
  LagrangianModel.Mixed.ofInvariantDensity p (action rF rB rI)
    (prolongation rF rB rI) (fun _ _ => rfl) (fieldEquiv rF rB) (fun _ => rfl) hp

end
end Math.StandardDensityAction
