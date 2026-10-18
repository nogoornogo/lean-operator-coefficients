import Math.LieGroups.E6.Minuscule.CorootLoops
import Math.Topology.CircleLoopLift
import Mathlib.Algebra.BigOperators.Pi

/-! Every identity-based loop of the actual torus contracts inside the
candidate. Negative and arbitrarily large windings are included. -/

set_option autoImplicit false

namespace Math.E6.Minuscule.Coroot

noncomputable section

open unitInterval

theorem hLine_int_mul (i : Fin 6) (n : ℤ) (t : ℝ) :
    hLine i ((n : ℝ) * t) = hLine i t ^ n := by
  let f : ℝ →+ Additive compactIdentityComponent :=
    { toFun := fun t => Additive.ofMul (hLine i t)
      map_zero' := hLine_zero i
      map_add' := hLine_add i }
  have h := congrArg Additive.toMul (map_zsmul f n t)
  change hLine i (n • t) = hLine i t ^ n at h
  simpa only [zsmul_eq_mul] using h

theorem filling_integer (i : Fin 6) (u : ℝ) (n : ℤ) : filling i u (n : ℝ) = 1 := by
  have hs : (hLine i Real.pi ^ n) * (hLine i Real.pi ^ n) = 1 := by
    rw [← (Commute.refl (hLine i Real.pi)).mul_zpow, hLine_pi_square, one_zpow]
  simp only [filling, hLine_int_mul]
  rw [((hLine_pi_commutes i _).zpow_left n).eq,
    mul_assoc (xLine i _) (hLine i Real.pi ^ n) (hLine i Real.pi ^ n),
    hs, mul_one, mul_inv_cancel]

end

end Math.E6.Minuscule.Coroot

namespace Math.E6.Minuscule.Torus

noncomputable section

open unitInterval

theorem phase_single (i : Fin 6) (t : ℝ) :
    phase (Pi.single i t) = Pi.mulSingle i (Circle.exp t) := by
  funext j
  by_cases h : i = j
  · subst j; simp [phase]
  · simp [phase, Pi.single_eq_of_ne (Ne.symm h), Pi.mulSingle_eq_of_ne (Ne.symm h)]

theorem hom_coordinate_product (z : Point) :
    (List.ofFn fun i : Fin 6 => hom (Pi.mulSingle i (z i))).prod = hom z := by
  change (List.ofFn (hom ∘ fun i : Fin 6 => Pi.mulSingle i (z i))).prod = _
  rw [← List.map_ofFn, ← map_list_prod, List.prod_ofFn, Finset.univ_prod_mulSingle]

def coordinateLoop (p : Path (1 : Point) 1) (i : Fin 6) : Path (1 : Circle) 1 :=
  p.map (continuous_apply i)

def loopImage (p : Path (1 : Point) 1) : Path (1 : compactIdentityComponent) 1 :=
  (p.map hom_continuous).cast (map_one hom).symm (map_one hom).symm

@[simp] theorem loopImage_apply (p : Path (1 : Point) 1) (s : I) :
    loopImage p s = hom (p s) := rfl

/-- Ordered products do not assume that intermediate fillings commute. -/
def loopFilling (p : Path (1 : Point) 1) (u s : I) : compactIdentityComponent :=
  (List.ofFn fun i : Fin 6 => Coroot.filling i (u : ℝ)
    (CircleLoopLift.turns (coordinateLoop p i) s)).prod

theorem loopFilling_continuous (p : Path (1 : Point) 1) :
    Continuous (fun q : I × I => loopFilling p q.1 q.2) := by
  have hc (i : Fin 6) : Continuous (fun q : I × I => Coroot.filling i (q.1 : ℝ)
      (CircleLoopLift.turns (coordinateLoop p i) q.2)) := by
    have h : Continuous (fun q : I × I =>
        ((q.1 : ℝ), CircleLoopLift.turns (coordinateLoop p i) q.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        ((CircleLoopLift.turns (coordinateLoop p i)).continuous.comp continuous_snd)
    have hl := (Coroot.filling_continuous i).comp h
    simpa only [Function.comp_def] using hl
  simpa only [loopFilling, List.ofFn_eq_map] using
    continuous_list_prod (List.finRange 6) (fun i _ => hc i)

theorem loopFilling_start (p : Path (1 : Point) 1) (s : I) :
    loopFilling p 0 s = hom (p s) := by
  have hf (i : Fin 6) : Coroot.filling i 0 (CircleLoopLift.turns (coordinateLoop p i) s) =
      hom (Pi.mulSingle i (p s i)) := by
    rw [Coroot.filling_start, Coroot.hLine_torus, phase_single, CircleLoopLift.exp_turns]
    rfl
  change (List.ofFn fun i : Fin 6 =>
    Coroot.filling i 0 (CircleLoopLift.turns (coordinateLoop p i) s)).prod = _
  simp only [hf, hom_coordinate_product]

theorem loopFilling_finish (p : Path (1 : Point) 1) (s : I) : loopFilling p 1 s = 1 := by
  simp [loopFilling, Coroot.filling_finish]

theorem loopFilling_source (p : Path (1 : Point) 1) (u : I) : loopFilling p u 0 = 1 := by
  simp [loopFilling, Coroot.filling_source]

theorem loopFilling_target (p : Path (1 : Point) 1) (u : I) : loopFilling p u 1 = 1 := by
  have hf (i : Fin 6) : Coroot.filling i (u : ℝ)
      (CircleLoopLift.turns (coordinateLoop p i) 1) = 1 := by
    obtain ⟨n, hn⟩ := CircleLoopLift.turns_one_integer (coordinateLoop p i)
    rw [hn, Coroot.filling_integer]
  simp only [loopFilling, hf]
  simp

/-- A filling of every actual torus loop, not only its coordinate generators. -/
def loopContraction (p : Path (1 : Point) 1) : (loopImage p).Homotopy (Path.refl 1) where
  toFun q := loopFilling p q.1 q.2
  continuous_toFun := loopFilling_continuous p
  map_zero_left s := loopFilling_start p s
  map_one_left s := loopFilling_finish p s
  prop' u s hs := by
    rcases hs with h | h
    · subst s
      change loopFilling p u 0 = (loopImage p) 0
      rw [Path.source]
      exact loopFilling_source p u
    · rw [Set.mem_singleton_iff] at h
      subst s
      change loopFilling p u 1 = (loopImage p) 1
      rw [Path.target]
      exact loopFilling_target p u

theorem loopImage_nullhomotopic (p : Path (1 : Point) 1) :
    (loopImage p).Homotopic (Path.refl 1) := ⟨loopContraction p⟩

end

end Math.E6.Minuscule.Torus
