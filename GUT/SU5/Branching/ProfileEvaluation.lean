import GUT.SU5.Branching.TorusMatterCharacter
import Physics.StandardModel.Spectrum.Charges.FiniteChargeProfiles

open Physics

open Math Math.SU5

/-! Evaluation of finite charge profiles on the actual SU(5) torus.
This is the target side of the retained-matter trace comparison. -/

set_option autoImplicit false

namespace GUT.SU5.ProfileEvaluation
open Physics.SU5

noncomputable section

open StandardAbelianCharge StandardSMCharacterTarget FiniteAbelianChargeSectors
open FiniteChargeProfiles TorusCharacter

variable {H : Type*} [CommGroup H]

def profileEval (p : ChargeLabel H →₀ ℕ) (h : H) : ℂ :=
  p.sum fun q n => (n : ℂ) * (q.toMul h : ℂ)

theorem eval_atWeight (w : ReducedWeight) (p : ChargeLabel H →₀ ℕ)
    (t : MaximalTorus.Torus) (h : H) :
    TorusCharacter.eval (atWeight w p) (t, h) = (weightCharacter w t : ℂ) * profileEval p h := by
  unfold atWeight TorusCharacter.eval
  rw [Finsupp.sum_mapDomain_index]
  · unfold integral
    rw [Finsupp.sum_mapRange_index]
    · simp only [keyCharacter_apply, Int.cast_natCast, profileEval, Finsupp.sum,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    · simp
  · simp
  · intros; simp [add_mul]

theorem eval_target (P : Profiles (ChargeLabel H)) (t : MaximalTorus.Torus) (h : H) :
    TorusCharacter.eval (target P) (t, h) = ∑ i : Fin 15,
      (weightCharacter (smReducedWeight i) t : ℂ) * profileEval (smCharge P i) h := by
  rw [← evalAddHom_apply, target, map_sum]
  simp only [evalAddHom_apply, eval_atWeight]

theorem eval_block_target (p q : ChargeLabel H →₀ ℕ) (t : MaximalTorus.Torus) (h : H) :
    TorusCharacter.eval (target (sectorCharges p q)) (t, h) =
      UnitaryMatter.ten.toRepresentation.character (MaximalTorus.hom t) * profileEval p h +
        UnitaryMatter.antifundamental.toRepresentation.character (MaximalTorus.hom t) *
          profileEval q h := by
  rw [eval_target, TorusMatterCharacter.weighted_character]
  apply Finset.sum_congr rfl
  intro i _
  fin_cases i <;> rfl

end

end GUT.SU5.ProfileEvaluation
