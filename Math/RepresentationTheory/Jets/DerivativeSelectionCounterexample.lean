import Math.RepresentationTheory.Jets.DerivativeProhibition

/-! Global target prohibition need not forbid the selected input.
The explicit unipotent action has a fixed line with no coefficient extension. -/
namespace Math.DerivativeSelectionCounterexample
set_option autoImplicit false
noncomputable section
open Representation DerivativeProhibition

abbrev H := Multiplicative ℂ
abbrev U := ℂ × ℂ
def action : Representation ℂ H U where
  toFun g := {
    toFun v := (v.1+g.toAdd*v.2,v.2)
    map_add' v w := by
      apply Prod.ext
      · change v.1+w.1+g.toAdd*(v.2+w.2) =
          (v.1+g.toAdd*v.2)+(w.1+g.toAdd*w.2)
        ring
      · rfl
    map_smul' c v := by
      apply Prod.ext
      · change c*v.1+g.toAdd*(c*v.2) = c*(v.1+g.toAdd*v.2)
        ring
      · rfl }
  map_one' := by apply LinearMap.ext; intro v; apply Prod.ext <;> simp
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · change v.1+(g.toAdd+h.toAdd)*v.2 = v.1+h.toAdd*v.2+g.toAdd*v.2
      ring
    · rfl

def input : DerivativeInterface.Input H U where
  action := action
  relations := ⊥
  stable g p hp := by change p = 0 at hp; subst p; exact map_zero _

def line : Submodule ℂ U := (LinearMap.snd ℂ ℂ ℂ).ker
theorem line_stable : ∀ g, line ≤ line.comap (input.action g) := fun _ _ hp => hp
def selected := input.select line line_stable
def e1 : U := (1,0)
def e2 : U := (0,1)
def firstVector : line := ⟨e1,rfl⟩

theorem global_first_zero (f : input.Coefficient) : f.val e1 = 0 := by
  have he := IntertwiningMap.isIntertwining _ _ f.val (Multiplicative.ofAdd (1:ℂ)) e2
  change f.val (action (Multiplicative.ofAdd (1:ℂ)) e2) = f.val e2 at he
  have ha : action (Multiplicative.ofAdd (1:ℂ)) e2 = e1+e2 := by
    ext <;> norm_num [action,e1,e2]
  rw [ha,map_add] at he
  exact add_right_cancel (he.trans (zero_add (f.val e2)).symm)

theorem global_target_forbids : TargetForbids input line := by
  intro f v
  have he : v.val = v.val.1 • e1 := by
    apply Prod.ext
    · simp [e1]
    · have h : v.val.2 = 0 := v.property
      simp [e1,h]
  rw [he,map_smul,global_first_zero,smul_zero]

def selectedWitness : selected.Coefficient := ⟨{
  toLinearMap := (LinearMap.fst ℂ ℂ ℂ).comp line.subtype
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    have hz : v.val.2 = 0 := v.property
    change v.val.1+g.toAdd*v.val.2 = v.val.1
    rw [hz,mul_zero,add_zero] }, by
      intro v hv
      have hz : v.val = 0 := hv
      change v.val.1 = 0
      rw [hz]
      rfl⟩

theorem selected_allows : Allows selected := by
  refine ⟨selectedWitness,?_⟩
  intro hz
  have h := congrArg (fun f : selected.Coefficient => f.val firstVector) hz
  change (1:ℂ) = 0 at h
  exact one_ne_zero h

theorem restriction_not_surjective : ¬ Function.Surjective (input.restrict line line_stable) :=
  restriction_obstruction input line line_stable global_target_forbids selected_allows

theorem extension_premise_required :
    TargetForbids input line ∧ ¬ Forbids selected := by
  refine ⟨global_target_forbids,?_⟩
  intro h
  obtain ⟨f,hf⟩ := selected_allows
  exact hf (h f)

end
end Math.DerivativeSelectionCounterexample
