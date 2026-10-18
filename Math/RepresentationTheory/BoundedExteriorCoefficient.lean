import Math.RepresentationTheory.GroupedExteriorPolynomial
import Math.RepresentationTheory.WeightStringExtraction

/-! Coefficient-only recurrence with proved linear support bounds. -/
namespace Math.BoundedExteriorCoefficient
set_option autoImplicit false
open ComputableWeightPolynomial
variable {W : Type*} [AddCommGroup W]
abbrev Test (W : Type*) [AddCommGroup W] := (ℤ × W) →+ ℤ

def lower (f : Test W) (ws : List W) : ℤ := (ws.map (fun w => min 0 (f (1,w)))).sum
def upper (f : Test W) (ws : List W) : ℤ := (ws.map (fun w => max 0 (f (1,w)))).sum

theorem mem_bounds (f : Test W) (ws : List W) (n : ℕ) (x : W × ℤ)
    (hx : x ∈ exterior ws n) : lower f ws ≤ f (n,x.1) ∧ f (n,x.1) ≤ upper f ws := by
  induction ws generalizing n x with
  | nil =>
    cases n with
    | zero =>
      simp only [exterior,List.mem_singleton] at hx
      subst x
      have hf : f ((0 : ℤ),(0 : W)) = 0 := f.map_zero
      simp [lower,upper,hf]
    | succ n => simp [exterior] at hx
  | cons w ws ih =>
    have hlo : min 0 (f (1,w)) ≤ 0 := min_le_left _ _
    have hhi : 0 ≤ max 0 (f (1,w)) := le_max_left _ _
    cases n with
    | zero =>
      have h := ih 0 x hx
      simp only [lower,upper,List.map_cons,List.sum_cons] at *
      constructor <;> omega
    | succ n =>
      simp only [exterior,List.mem_append] at hx
      rcases hx with hx | hx
      · have h := ih (n+1) x hx
        simp only [lower,upper,List.map_cons,List.sum_cons] at *
        constructor <;> omega
      · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
        have h := ih n y hy
        have hf : f ((n+1 : ℕ), w+y.1) = f (1,w) + f (n,y.1) := by
          rw [show (((n+1 : ℕ) : ℤ), w+y.1) = (1,w)+((n : ℤ),y.1) by
            ext <;> simp [add_comm]]
          exact f.map_add _ _
        have hlow := min_le_right (0 : ℤ) (f (1,w))
        have hhigh := le_max_right (0 : ℤ) (f (1,w))
        simp only [lower,upper,List.map_cons,List.sum_cons] at *
        rw [hf]
        constructor <;> omega

theorem coefficient_zero [DecidableEq W] (f : Test W) (ws : List W) (n : ℕ) (w : W)
    (h : ¬ (lower f ws ≤ f (n,w) ∧ f (n,w) ≤ upper f ws)) :
    coefficient (exterior ws n) w = 0 := by
  unfold coefficient
  apply List.sum_eq_zero
  intro a ha
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
  split
  · next he => exact False.elim (h (he ▸ mem_bounds f ws n x hx))
  · rfl

theorem lower_slots (f : Test W) (ws : List W) :
    lower f (GroupedExteriorPolynomial.slots ws) = 3 * lower f ws := by
  induction ws with
  | nil => simp [lower,GroupedExteriorPolynomial.slots]
  | cons w ws ih =>
    simp only [GroupedExteriorPolynomial.slots,List.flatMap_cons,List.cons_append,List.nil_append,
      lower,List.map_cons,List.sum_cons] at *
    omega

theorem upper_slots (f : Test W) (ws : List W) :
    upper f (GroupedExteriorPolynomial.slots ws) = 3 * upper f ws := by
  induction ws with
  | nil => simp [upper,GroupedExteriorPolynomial.slots]
  | cons w ws ih =>
    simp only [GroupedExteriorPolynomial.slots,List.flatMap_cons,List.cons_append,List.nil_append,
      upper,List.map_cons,List.sum_cons] at *
    omega

/-- The bounds may be computed once per remaining slot list. -/
def bounds (fs : List (Test W)) (ws : List W) : List (Test W × ℤ × ℤ) :=
  fs.map (fun f => (f,3*lower f ws,3*upper f ws))

def possible (bs : List (Test W × ℤ × ℤ)) (n : ℕ) (w : W) : Bool :=
  bs.all (fun b => decide (b.2.1 ≤ b.1 (n,w) ∧ b.1 (n,w) ≤ b.2.2))

theorem impossible_zero [DecidableEq W] (fs : List (Test W)) (ws : List W) (n : ℕ) (w : W)
    (h : possible (bounds fs ws) n w = false) :
    coefficient (exterior (GroupedExteriorPolynomial.slots ws) n) w = 0 := by
  have hn : ¬ ∀ f ∈ fs, 3*lower f ws ≤ f (n,w) ∧ f (n,w) ≤ 3*upper f ws := by
    simpa [possible,bounds,List.all_eq_true] using h
  push Not at hn
  obtain ⟨f,hf,hbad⟩ := hn
  apply coefficient_zero f
  simp only [lower_slots,upper_slots]
  omega

def step (a : W) (prev : ℕ → W → ℤ) : ℕ → W → ℤ
  | 0,w => prev 0 w
  | 1,w => prev 1 w + 3*prev 0 (w-a)
  | 2,w => prev 2 w + 3*prev 1 (w-a) + 3*prev 0 (w-(a+a))
  | n+3,w => prev (n+3) w + 3*prev (n+2) (w-a) + 3*prev (n+1) (w-(a+a)) +
      prev n (w-(a+a+a))

def compute [DecidableEq W] (fs : List (Test W)) (ws : List W) : ℕ → W → ℤ :=
  List.rec (motive := fun _ => ℕ → W → ℤ)
    (fun n w => if n=0 ∧ w=0 then 1 else 0)
    (fun a tail prev =>
      let bs := bounds fs (a::tail)
      fun n w => if possible bs n w then step a prev n w else 0) ws

theorem compute_cons [DecidableEq W] (fs : List (Test W)) (a : W) (ws : List W)
    (n : ℕ) (w : W) : compute fs (a::ws) n w =
      if possible (bounds fs (a::ws)) n w then step a (compute fs ws) n w else 0 := rfl

theorem coefficient_step [DecidableEq W] (a : W) (ws : List W) (n : ℕ) (w : W) :
    coefficient (exterior (a::a::a::ws) n) w =
      step a (fun n w => coefficient (exterior ws n) w) n w := by
  have hs (p : Terms W) (a w : W) : coefficient (shift a p) w = coefficient p (w-a) := by
    simpa only [shift,one_mul] using WeightStringExtraction.coefficient_scaledShift p a w 1
  rcases n with _ | _ | _ | n
  all_goals simp only [step,exterior,WeightStringExtraction.coefficient_append,hs]
  all_goals try simp only [sub_sub,Nat.add_assoc]
  all_goals ring

theorem compute_eq [DecidableEq W] (fs : List (Test W)) (ws : List W) (n : ℕ) (w : W) :
    compute fs ws n w = coefficient (exterior (GroupedExteriorPolynomial.slots ws) n) w := by
  induction ws generalizing n w with
  | nil => cases n <;> simp [compute,GroupedExteriorPolynomial.slots,exterior,coefficient,eq_comm]
  | cons a ws ih =>
    change (if possible (bounds fs (a::ws)) n w then step a (compute fs ws) n w else 0) = _
    split
    · have he : compute fs ws = fun n w => coefficient (exterior (GroupedExteriorPolynomial.slots ws) n) w :=
        funext (fun n => funext (ih n))
      rw [he]
      exact (coefficient_step a (GroupedExteriorPolynomial.slots ws) n w).symm
    · next h => exact (impossible_zero fs (a::ws) n w (by simpa using h)).symm

end Math.BoundedExteriorCoefficient
