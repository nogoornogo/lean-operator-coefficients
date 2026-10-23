import GUT.SU5.SelectionRules.ScalarBlockQque

open Physics

/-! Independent complex mass rows on two actual tens and one dual ten.
The common scalar residual character is preserved; the mass need only be
SM/H invariant. Zero modes are derived, not supplied. -/
namespace GUT.SU5.MixedTenMass
set_option autoImplicit false
noncomputable section
open Math Representation StandardModelEmbedding Matter ExteriorSquareBranching
open StandardSMGaugeTensor SMEpsilonTensor InvariantWeylMass
local instance : AddCommGroup Quark := inferInstance
local instance : AddCommGroup Ten := inferInstance

structure RowWeights where
  up : ℂ
  quark : ℂ
  electron : ℂ

variable {H : Type*} [CommGroup H]

def weightedBlocks (r : RowWeights) : IntertwiningMap blocksRho blocksRho where
  toLinearMap := (r.up • (LinearMap.id : Module.Dual ℂ Color →ₗ[ℂ] _)).prodMap
    ((r.quark • (LinearMap.id : Quark →ₗ[ℂ] _)).prodMap
      (r.electron • (LinearMap.id : Module.Dual ℂ ℂ →ₗ[ℂ] _)))
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    simp [blocksRho]

def weighted (r : RowWeights) : IntertwiningMap (ten.comp hom) (ten.comp hom) :=
  tenEquiv.symm.toIntertwiningMap.comp ((weightedBlocks r).comp tenEquiv.toIntertwiningMap)

theorem weighted_apply (r : RowWeights) (x : Ten) :
    weighted r x = tenEquiv.toLinearEquiv.symm
      (r.up • (tenEquiv x).1, (r.quark • (tenEquiv x).2.1,
        r.electron • (tenEquiv x).2.2)) := rfl

def tenRho (chi : H →* Circle) := StandardSMResidualTensor.charged (ten.comp hom) chi
def barRho (psi : H →* Circle) := StandardSMResidualTensor.charged (antifundamental.comp hom) psi

def chargedWeighted (chi : H →* Circle) (r : RowWeights) :
    IntertwiningMap (tenRho chi) (tenRho chi) where
  toLinearMap := (weighted r).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change weighted r ((chi g.2 : ℂ) • ten (hom g.1) x) =
      (chi g.2 : ℂ) • ten (hom g.1) (weighted r x)
    rw [map_smul]
    exact congrArg (fun z => (chi g.2 : ℂ) • z)
      ((weighted r).isIntertwining _ _ g.1 x)

abbrev Source := (Ten × BarFive) × Ten
abbrev Fields := Source × Module.Dual ℂ Ten

def sourceRho (chi psi : H →* Circle) := ((tenRho chi).prod (barRho psi)).prod (tenRho chi)
def fieldsRho (chi psi : H →* Circle) := (sourceRho chi psi).prod (tenRho chi).dual

def massMap (chi psi : H →* Circle) (a b : RowWeights) :
    IntertwiningMap (sourceRho chi psi) (tenRho chi) :=
  (chargedWeighted chi a).comp
    ((IntertwiningMap.fst ℂ (tenRho chi) (barRho psi)).comp
      (IntertwiningMap.fst ℂ ((tenRho chi).prod (barRho psi)) (tenRho chi))) +
  (chargedWeighted chi b).comp
    (IntertwiningMap.snd ℂ ((tenRho chi).prod (barRho psi)) (tenRho chi))

theorem massMap_apply (chi psi : H →* Circle) (a b : RowWeights) (x : Source) :
    massMap chi psi a b x = weighted a x.1.1 + weighted b x.2 := rfl

def mass (chi psi : H →* Circle) (a b : RowWeights) := ofDirac (massMap chi psi a b)

theorem mem_radical_iff (chi psi : H →* Circle) (a b : RowWeights) (x : Fields) :
    x ∈ (mass chi psi a b).radical.toSubmodule ↔
      massMap chi psi a b x.1 = 0 ∧ ∀ v, x.2 (massMap chi psi a b v) = 0 :=
  DiracWeylConvention.mem_radical_iff _ _

/-- A zero row retains the original copy. Otherwise use (beta,-alpha),
which is nonzero for every nonzero row, without normalization or division. -/
def kernelFirst (alpha beta : ℂ) : ℂ := if alpha = 0 ∧ beta = 0 then 1 else beta
def kernelSecond (alpha beta : ℂ) : ℂ := if alpha = 0 ∧ beta = 0 then 0 else -alpha

theorem kernel_relation (alpha beta : ℂ) :
    alpha * kernelFirst alpha beta + beta * kernelSecond alpha beta = 0 := by
  by_cases h : alpha = 0 ∧ beta = 0
  · simp [kernelFirst, kernelSecond, h]
  · simp [kernelFirst, kernelSecond, h]; ring

theorem kernel_nonzero (alpha beta : ℂ) :
    kernelFirst alpha beta ≠ 0 ∨ kernelSecond alpha beta ≠ 0 := by
  by_cases h : alpha = 0 ∧ beta = 0
  · simp [kernelFirst, h]
  · simp only [kernelFirst, kernelSecond, ite_eq_right h, neg_ne_zero]
    tauto

def tenSlot (x : Blocks) : Ten := tenEquiv.toLinearEquiv.symm x

def lightMap {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : V →ₗ[ℂ] Ten) (alpha beta : ℂ) : V →ₗ[ℂ] Fields where
  toFun x := (((kernelFirst alpha beta • f x, 0), kernelSecond alpha beta • f x), 0)
  map_add' x y := by simp [map_add, smul_add]
  map_smul' z x := by simp [map_smul, smul_smul, mul_comm]

theorem lightMap_injective {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : V →ₗ[ℂ] Ten) (hf : Function.Injective f) (alpha beta : ℂ) :
    Function.Injective (lightMap f alpha beta) := by
  intro x y h
  rcases kernel_nonzero alpha beta with hfirst | hsecond
  · apply hf
    exact (smul_right_injective _ hfirst) (congrArg (fun z : Fields => z.1.1.1) h)
  · apply hf
    exact (smul_right_injective _ hsecond) (congrArg (fun z : Fields => z.1.2) h)

def quarkTen : Quark →ₗ[ℂ] Ten := tenEquiv.toLinearEquiv.symm.toLinearMap.comp ((LinearMap.inr ℂ (Module.Dual ℂ Color) (Quark × Module.Dual ℂ ℂ)).comp (LinearMap.inl ℂ Quark (Module.Dual ℂ ℂ)))

theorem quarkTen_injective : Function.Injective quarkTen := by
  intro x y h
  have he := tenEquiv.toLinearEquiv.symm.injective h
  exact congrArg (fun z : Blocks => z.2.1) he

def quarkLinear (a b : RowWeights) := lightMap quarkTen a.quark b.quark

theorem quark_injective (a b : RowWeights) : Function.Injective (quarkLinear a b) :=
  lightMap_injective quarkTen quarkTen_injective _ _

theorem quark_weighted (r : RowWeights) (x : Quark) :
    weighted r (quarkTen x) = r.quark • quarkTen x := by
  apply tenEquiv.toLinearEquiv.injective
  change tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm _) = _
  rw [LinearEquiv.apply_symm_apply, map_smul]
  change _ = r.quark • tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm (0, (x, 0)))
  rw [LinearEquiv.apply_symm_apply]
  change (r.up • (tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm (0, (x, 0)))).1,
    (r.quark • (tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm (0, (x, 0)))).2.1,
      r.electron • (tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm (0, (x, 0)))).2.2)) = _
  rw [LinearEquiv.apply_symm_apply]
  simp

theorem quark_light (chi psi : H →* Circle) (a b : RowWeights) (x : Quark) :
    quarkLinear a b x ∈ (mass chi psi a b).radical.toSubmodule := by
  rw [mem_radical_iff]
  constructor
  · change weighted a (kernelFirst a.quark b.quark • quarkTen x) +
      weighted b (kernelSecond a.quark b.quark • quarkTen x) = 0
    rw [map_smul, map_smul, quark_weighted, quark_weighted, smul_smul, smul_smul,
      ← add_smul]
    have he := kernel_relation a.quark b.quark
    rw [mul_comm (kernelFirst _ _) _, mul_comm (kernelSecond _ _) _, he, zero_smul]
  · intro v
    rfl

theorem quarkTen_action (g : GaugeGroup) (x : Quark) :
    ten (hom g) (quarkTen x) = quarkTen (quark g x) := by
  apply tenEquiv.toLinearEquiv.injective
  have he := tenEquiv.toIntertwiningMap.isIntertwining _ _ g
    (tenEquiv.toLinearEquiv.symm (0, (x, 0)))
  change tenEquiv.toLinearEquiv (ten (hom g) (tenEquiv.toLinearEquiv.symm (0, (x, 0)))) =
    blocksRho g (tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm (0, (x, 0)))) at he
  rw [LinearEquiv.apply_symm_apply] at he
  change tenEquiv.toLinearEquiv (ten (hom g) (tenEquiv.toLinearEquiv.symm (0, (x, 0)))) = tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm _)
  rw [LinearEquiv.apply_symm_apply]
  simpa [blocksRho, Prod.zero_eq_mk] using he

theorem quark_action (chi psi : H →* Circle) (a b : RowWeights)
    (g : GaugeGroup × H) (x : Quark) :
    fieldsRho chi psi g (quarkLinear a b x) =
      quarkLinear a b (StandardSMResidualTensor.charged quark chi g x) := by
  change (((((chi g.2 : ℂ) • ten (hom g.1) (kernelFirst a.quark b.quark • quarkTen x)),
      (barRho psi g) 0),
      (chi g.2 : ℂ) • ten (hom g.1) (kernelSecond a.quark b.quark • quarkTen x)),
      ((tenRho chi).dual g) 0) = _
  simp [map_smul, map_zero, quarkTen_action, quarkLinear, lightMap,
    StandardSMResidualTensor.charged, smul_smul, mul_comm]

def upTen : Module.Dual ℂ Color →ₗ[ℂ] Ten := tenEquiv.toLinearEquiv.symm.toLinearMap.comp (LinearMap.inl ℂ (Module.Dual ℂ Color) (Quark × Module.Dual ℂ ℂ))

theorem upTen_injective : Function.Injective upTen := by
  intro x y h
  have he := tenEquiv.toLinearEquiv.symm.injective h
  exact congrArg (fun z : Blocks => z.1) he

def upLinear (a b : RowWeights) := lightMap upTen a.up b.up

theorem up_injective (a b : RowWeights) : Function.Injective (upLinear a b) :=
  lightMap_injective upTen upTen_injective _ _

theorem up_weighted (r : RowWeights) (x : Module.Dual ℂ Color) :
    weighted r (upTen x) = r.up • upTen x := by
  apply tenEquiv.toLinearEquiv.injective
  change tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm _) = _
  rw [LinearEquiv.apply_symm_apply, map_smul]
  change _ = r.up • tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm (x, 0))
  rw [LinearEquiv.apply_symm_apply]
  change (r.up • (tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm (x, 0))).1,
    (r.quark • (tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm (x, 0))).2.1,
      r.electron • (tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm (x, 0))).2.2)) = _
  rw [LinearEquiv.apply_symm_apply]
  simp [Prod.zero_eq_mk]

theorem up_light (chi psi : H →* Circle) (a b : RowWeights) (x : Module.Dual ℂ Color) :
    upLinear a b x ∈ (mass chi psi a b).radical.toSubmodule := by
  rw [mem_radical_iff]
  constructor
  · change weighted a (kernelFirst a.up b.up • upTen x) +
      weighted b (kernelSecond a.up b.up • upTen x) = 0
    rw [map_smul, map_smul, up_weighted, up_weighted, smul_smul, smul_smul,
      ← add_smul]
    have he := kernel_relation a.up b.up
    rw [mul_comm (kernelFirst _ _) _, mul_comm (kernelSecond _ _) _, he, zero_smul]
  · intro v
    rfl

theorem upTen_action (g : GaugeGroup) (x : Module.Dual ℂ Color) :
    ten (hom g) (upTen x) = upTen (upRight.dual g x) := by
  apply tenEquiv.toLinearEquiv.injective
  have he := tenEquiv.toIntertwiningMap.isIntertwining _ _ g
    (tenEquiv.toLinearEquiv.symm (x, 0))
  change tenEquiv.toLinearEquiv (ten (hom g) (tenEquiv.toLinearEquiv.symm (x, 0))) =
    blocksRho g (tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm (x, 0))) at he
  rw [LinearEquiv.apply_symm_apply] at he
  change tenEquiv.toLinearEquiv (ten (hom g) (tenEquiv.toLinearEquiv.symm (x, 0))) = tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm _)
  rw [LinearEquiv.apply_symm_apply]
  simpa [blocksRho, Prod.zero_eq_mk] using he

theorem up_action (chi psi : H →* Circle) (a b : RowWeights)
    (g : GaugeGroup × H) (x : Module.Dual ℂ Color) :
    fieldsRho chi psi g (upLinear a b x) =
      upLinear a b (StandardSMResidualTensor.charged upRight.dual chi g x) := by
  change (((((chi g.2 : ℂ) • ten (hom g.1) (kernelFirst a.up b.up • upTen x)),
      (barRho psi g) 0),
      (chi g.2 : ℂ) • ten (hom g.1) (kernelSecond a.up b.up • upTen x)),
      ((tenRho chi).dual g) 0) = _
  simp [map_smul, map_zero, upTen_action, upLinear, lightMap,
    StandardSMResidualTensor.charged, smul_smul, mul_comm]

def electronTen : Module.Dual ℂ ℂ →ₗ[ℂ] Ten := tenEquiv.toLinearEquiv.symm.toLinearMap.comp ((LinearMap.inr ℂ (Module.Dual ℂ Color) (Quark × Module.Dual ℂ ℂ)).comp (LinearMap.inr ℂ Quark (Module.Dual ℂ ℂ)))

theorem electronTen_injective : Function.Injective electronTen := by
  intro x y h
  have he := tenEquiv.toLinearEquiv.symm.injective h
  exact congrArg (fun z : Blocks => z.2.2) he

def electronLinear (a b : RowWeights) := lightMap electronTen a.electron b.electron

theorem electron_injective (a b : RowWeights) : Function.Injective (electronLinear a b) :=
  lightMap_injective electronTen electronTen_injective _ _

theorem electron_weighted (r : RowWeights) (x : Module.Dual ℂ ℂ) :
    weighted r (electronTen x) = r.electron • electronTen x := by
  apply tenEquiv.toLinearEquiv.injective
  change tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm _) = _
  rw [LinearEquiv.apply_symm_apply, map_smul]
  change _ = r.electron • tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm (0, (0, x)))
  rw [LinearEquiv.apply_symm_apply]
  change (r.up • (tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm (0, (0, x)))).1,
    (r.quark • (tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm (0, (0, x)))).2.1,
      r.electron • (tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm (0, (0, x)))).2.2)) = _
  rw [LinearEquiv.apply_symm_apply]
  simp

theorem electron_light (chi psi : H →* Circle) (a b : RowWeights) (x : Module.Dual ℂ ℂ) :
    electronLinear a b x ∈ (mass chi psi a b).radical.toSubmodule := by
  rw [mem_radical_iff]
  constructor
  · change weighted a (kernelFirst a.electron b.electron • electronTen x) +
      weighted b (kernelSecond a.electron b.electron • electronTen x) = 0
    rw [map_smul, map_smul, electron_weighted, electron_weighted, smul_smul, smul_smul,
      ← add_smul]
    have he := kernel_relation a.electron b.electron
    rw [mul_comm (kernelFirst _ _) _, mul_comm (kernelSecond _ _) _, he, zero_smul]
  · intro v
    rfl

theorem electronTen_action (g : GaugeGroup) (x : Module.Dual ℂ ℂ) :
    ten (hom g) (electronTen x) = electronTen (electronRight.dual g x) := by
  apply tenEquiv.toLinearEquiv.injective
  have he := tenEquiv.toIntertwiningMap.isIntertwining _ _ g
    (tenEquiv.toLinearEquiv.symm (0, (0, x)))
  change tenEquiv.toLinearEquiv (ten (hom g) (tenEquiv.toLinearEquiv.symm (0, (0, x)))) =
    blocksRho g (tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm (0, (0, x)))) at he
  rw [LinearEquiv.apply_symm_apply] at he
  change tenEquiv.toLinearEquiv (ten (hom g) (tenEquiv.toLinearEquiv.symm (0, (0, x)))) = tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm _)
  rw [LinearEquiv.apply_symm_apply]
  simpa [blocksRho, Prod.zero_eq_mk] using he

theorem electron_action (chi psi : H →* Circle) (a b : RowWeights)
    (g : GaugeGroup × H) (x : Module.Dual ℂ ℂ) :
    fieldsRho chi psi g (electronLinear a b x) =
      electronLinear a b (StandardSMResidualTensor.charged electronRight.dual chi g x) := by
  change (((((chi g.2 : ℂ) • ten (hom g.1) (kernelFirst a.electron b.electron • electronTen x)),
      (barRho psi g) 0),
      (chi g.2 : ℂ) • ten (hom g.1) (kernelSecond a.electron b.electron • electronTen x)),
      ((tenRho chi).dual g) 0) = _
  simp [map_smul, map_zero, electronTen_action, electronLinear, lightMap,
    StandardSMResidualTensor.charged, smul_smul, mul_comm]


def Active (a b : RowWeights) : Prop :=
  (a.up ≠ 0 ∨ b.up ≠ 0) ∧ (a.quark ≠ 0 ∨ b.quark ≠ 0) ∧
    (a.electron ≠ 0 ∨ b.electron ≠ 0)

def rightFirst (alpha : ℂ) : ℂ := if alpha = 0 then 0 else alpha⁻¹
def rightSecond (alpha beta : ℂ) : ℂ := if alpha = 0 then beta⁻¹ else 0

theorem right_relation (alpha beta : ℂ) (h : alpha ≠ 0 ∨ beta ≠ 0) :
    alpha * rightFirst alpha + beta * rightSecond alpha beta = 1 := by
  by_cases ha : alpha = 0
  · have hb : beta ≠ 0 := h.resolve_left (not_not_intro ha)
    simp [rightFirst, rightSecond, ha, hb]
  · simp [rightFirst, rightSecond, ha]

def rightA (a : RowWeights) : RowWeights :=
  ⟨rightFirst a.up, rightFirst a.quark, rightFirst a.electron⟩
def rightB (a b : RowWeights) : RowWeights :=
  ⟨rightSecond a.up b.up, rightSecond a.quark b.quark, rightSecond a.electron b.electron⟩

theorem branch_weighted (r : RowWeights) (x : Ten) :
    tenEquiv.toLinearEquiv (weighted r x) =
      (r.up • (tenEquiv.toLinearEquiv x).1,
        (r.quark • (tenEquiv.toLinearEquiv x).2.1,
          r.electron • (tenEquiv.toLinearEquiv x).2.2)) := by
  change tenEquiv.toLinearEquiv (tenEquiv.toLinearEquiv.symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem massMap_surjective (chi psi : H →* Circle) (a b : RowWeights) (h : Active a b) :
    Function.Surjective (massMap chi psi a b) := by
  intro x
  refine ⟨((weighted (rightA a) x, 0), weighted (rightB a b) x), ?_⟩
  rw [massMap_apply]
  apply tenEquiv.toLinearEquiv.injective
  rw [map_add, branch_weighted, branch_weighted, branch_weighted, branch_weighted]
  simp only [rightA, rightB, smul_smul]
  apply Prod.ext
  · simp only [Prod.fst_add]
    rw [← add_smul, right_relation _ _ h.1, one_smul]
  · apply Prod.ext
    · simp only [Prod.fst_add, Prod.snd_add]
      rw [← add_smul, right_relation _ _ h.2.1, one_smul]
    · simp only [Prod.snd_add]
      rw [← add_smul, right_relation _ _ h.2.2, one_smul]

theorem active_radical_iff (chi psi : H →* Circle) (a b : RowWeights) (h : Active a b)
    (x : Fields) : x ∈ (mass chi psi a b).radical.toSubmodule ↔
      massMap chi psi a b x.1 = 0 ∧ x.2 = 0 := by
  rw [mem_radical_iff]
  constructor
  · rintro ⟨hx, hp⟩
    refine ⟨hx, LinearMap.ext fun v => ?_⟩
    obtain ⟨w, hw⟩ := massMap_surjective chi psi a b h v
    simpa [hw] using hp w
  · rintro ⟨hx, hp⟩
    exact ⟨hx, by intro v; rw [hp]; rfl⟩

theorem active_radical_finrank (chi psi : H →* Circle) (a b : RowWeights) (h : Active a b) :
    Module.finrank ℂ (mass chi psi a b).radical.toSubmodule = 15 := by
  have hr : LinearMap.range (massMap chi psi a b).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr (massMap_surjective chi psi a b h)
  have hn := LinearMap.finrank_range_add_finrank_ker (massMap chi psi a b).toLinearMap
  rw [hr] at hn
  simp [Module.finrank_prod, Nat.choose] at hn
  change Module.finrank ℂ (DiracWeylConvention.radical (massMap chi psi a b).toLinearMap) = _
  rw [(DiracWeylConvention.radicalLinearEquiv (massMap chi psi a b).toLinearMap).finrank_eq,
    Module.finrank_prod, hr, Submodule.dualAnnihilator_top]
  have hk : Module.finrank ℂ (LinearMap.ker (massMap chi psi a b).toLinearMap) = 15 := by omega
  simpa using hk

theorem mass_nonzero_of_witness (chi psi : H →* Circle) (a b : RowWeights)
    (x : Source) (hx : massMap chi psi a b x ≠ 0) : (mass chi psi a b).form ≠ 0 := by
  obtain ⟨phi, hphi⟩ := Module.Projective.exists_dual_eq_one ℂ hx
  intro hz
  have he := LinearMap.congr_fun (LinearMap.congr_fun hz (x, 0)) (0, phi)
  change phi (massMap chi psi a b x) + (0 : Module.Dual ℂ Ten) (massMap chi psi a b 0) = 0 at he
  simp [hphi] at he

theorem active_mass_nonzero (chi psi : H →* Circle) (a b : RowWeights) (h : Active a b) :
    (mass chi psi a b).form ≠ 0 := by
  have hn : Nontrivial Ten := Module.nontrivial_of_finrank_pos (R := ℂ) (by simp [Nat.choose])
  obtain ⟨x, hx⟩ := exists_ne (0 : Ten)
  obtain ⟨y, hy⟩ := massMap_surjective chi psi a b h x
  exact mass_nonzero_of_witness chi psi a b y (hy ▸ hx)

def mixedA : RowWeights := ⟨0, 1, 1⟩
def mixedB : RowWeights := ⟨1, 0, 1⟩
def unmixedA : RowWeights := ⟨0, 0, 0⟩
def unmixedB : RowWeights := ⟨1, 1, 1⟩
def partialB : RowWeights := ⟨0, 1, 1⟩

theorem mixed_active : Active mixedA mixedB := by
  norm_num [Active, mixedA, mixedB]

theorem mixed_mass_nonzero (chi psi : H →* Circle) :
    (mass chi psi mixedA mixedB).form ≠ 0 := by
  apply mass_nonzero_of_witness chi psi mixedA mixedB
    ((electronTen (LinearMap.id : ℂ →ₗ[ℂ] ℂ), 0), 0)
  rw [massMap_apply]
  simp only [map_zero, add_zero, electron_weighted]
  change (1 : ℂ) • electronTen (LinearMap.id : ℂ →ₗ[ℂ] ℂ) ≠ 0
  rw [one_smul]
  intro hz
  have he := electronTen_injective (hz.trans (map_zero electronTen).symm)
  have hone := LinearMap.congr_fun he 1
  norm_num at hone


def zeroWeights : RowWeights := ⟨0, 0, 0⟩

theorem weighted_zero (x : Ten) : weighted zeroWeights x = 0 := by
  apply tenEquiv.toLinearEquiv.injective
  rw [branch_weighted, map_zero]
  simp [zeroWeights]

theorem mass_apply (chi psi : H →* Circle) (a b : RowWeights) (x y : Fields) :
    (mass chi psi a b).form x y =
      y.2 (massMap chi psi a b x.1) + x.2 (massMap chi psi a b y.1) := rfl

theorem zero_form (chi psi : H →* Circle) : (mass chi psi zeroWeights zeroWeights).form = 0 := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rw [mass_apply, massMap_apply, massMap_apply, weighted_zero, weighted_zero,
    weighted_zero, weighted_zero]
  simp

theorem zero_radical_finrank (chi psi : H →* Circle) :
    Module.finrank ℂ (mass chi psi zeroWeights zeroWeights).radical.toSubmodule = 35 := by
  have hr : (mass chi psi zeroWeights zeroWeights).radical.toSubmodule = ⊤ := by
    apply top_unique
    intro x hx
    rw [SymmetricMass.mem_radical]
    intro y
    rw [zero_form]
    rfl
  rw [hr]
  simp [Module.finrank_prod, Nat.choose]

theorem partial_extra_up_light (chi psi : H →* Circle) (x : Module.Dual ℂ Color) :
    (((0, 0), upTen x), 0) ∈ (mass chi psi unmixedA partialB).radical.toSubmodule := by
  rw [mem_radical_iff]
  constructor
  · change weighted unmixedA 0 + weighted partialB (upTen x) = 0
    rw [map_zero, up_weighted]
    simp [partialB]
  · intro v
    rfl

theorem partial_mass_nonzero (chi psi : H →* Circle) :
    (mass chi psi unmixedA partialB).form ≠ 0 := by
  apply mass_nonzero_of_witness chi psi unmixedA partialB
    ((0, 0), electronTen (LinearMap.id : ℂ →ₗ[ℂ] ℂ))
  rw [massMap_apply]
  simp only [map_zero, zero_add, electron_weighted]
  change (1 : ℂ) • electronTen (LinearMap.id : ℂ →ₗ[ℂ] ℂ) ≠ 0
  rw [one_smul]
  intro hz
  have he := electronTen_injective (hz.trans (map_zero electronTen).symm)
  have hone := LinearMap.congr_fun he 1
  norm_num at hone

/-- A specified affine splitting pattern. This definition does not assert
that a UV adjoint Yukawa coupling has been constructed. -/
def affineRow (m y : ℂ) : RowWeights := ⟨m + 4*y, m - y, m - 6*y⟩

theorem affine_control_active : Active (affineRow 0 1) (affineRow 1 0) := by
  norm_num [Active, affineRow]


section RangeTransport
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def rangeCoords (f : V →ₗ[ℂ] Fields) (hf : Function.Injective f) :
    LinearMap.range f ≃ₗ[ℂ] V := (LinearEquiv.ofInjective f hf).symm

def rangeRho (f : V →ₗ[ℂ] Fields) (hf : Function.Injective f)
    (rho : Representation ℂ (GaugeGroup × H) V) :=
  RepresentationConjugation.pullback (rangeCoords f hf) rho

theorem range_coords (f : V →ₗ[ℂ] Fields) (hf : Function.Injective f)
    (x : LinearMap.range f) : f (rangeCoords f hf x) = x.val :=
  congrArg Subtype.val ((rangeCoords f hf).symm_apply_apply x)

theorem range_action (f : V →ₗ[ℂ] Fields) (hf : Function.Injective f)
    (rho : Representation ℂ (GaugeGroup × H) V) (chi psi : H →* Circle)
    (he : ∀ g x, fieldsRho chi psi g (f x) = f (rho g x))
    (g : GaugeGroup × H) (x : LinearMap.range f) :
    (rangeRho f hf rho g x).val = fieldsRho chi psi g x.val := by
  rw [rangeRho, RepresentationConjugation.pullback_apply]
  change f (rho g (rangeCoords f hf x)) = _
  rw [← he, range_coords]

end RangeTransport

variable (chi psi : H →* Circle) (a b : RowWeights)

/-- The d/L helper entries are unused, not a statement about psi. -/
def charges : StandardBranchProtonObstruction.Charges
    (Math.FiniteAbelianChargeSectors.ChargeLabel H) where
  quark := Additive.ofMul chi
  up := Additive.ofMul chi
  electron := Additive.ofMul chi
  down := 0
  lepton := 0

theorem neutral : FiniteAbelianChargeSectors.protonFirstCharacter (charges chi) = 1 :=
  NeutralQqueExterior.neutral_of_pointwise_block (charges chi)
    (fun h => chi h) (fun _ => 1) (fun _ => 1)
    (by intro h; simp [charges]) (by intro h; simp [charges]) (by intro h; simp [charges])

abbrev QuarkSpace := LinearMap.range (quarkLinear a b)
abbrev UpSpace := LinearMap.range (upLinear a b)
abbrev ElectronSpace := LinearMap.range (electronLinear a b)

local instance : AddCommGroup (QuarkSpace a b) := inferInstance
local instance : AddCommGroup (UpSpace a b) := inferInstance
local instance : AddCommGroup (ElectronSpace a b) := inferInstance

def quarkRho := rangeRho (quarkLinear a b) (quark_injective a b)
  (StandardSMResidualTensor.charged quark chi)
def upLeftRho := rangeRho (upLinear a b) (up_injective a b)
  (StandardSMResidualTensor.charged upRight.dual chi)
def electronLeftRho := rangeRho (electronLinear a b) (electron_injective a b)
  (StandardSMResidualTensor.charged electronRight.dual chi)

theorem quarkSpace_light (x : QuarkSpace a b) :
    x.val ∈ (mass chi psi a b).radical.toSubmodule := by
  obtain ⟨y, hy⟩ := x.property
  rw [← hy]
  exact quark_light chi psi a b y

theorem quarkSpace_action (g : GaugeGroup × H) (x : QuarkSpace a b) :
    (quarkRho chi a b g x).val = fieldsRho chi psi g x.val :=
  range_action _ _ _ chi psi (quark_action chi psi a b) g x

theorem upSpace_light (x : UpSpace a b) :
    x.val ∈ (mass chi psi a b).radical.toSubmodule := by
  obtain ⟨y, hy⟩ := x.property
  rw [← hy]
  exact up_light chi psi a b y

theorem upSpace_action (g : GaugeGroup × H) (x : UpSpace a b) :
    (upLeftRho chi a b g x).val = fieldsRho chi psi g x.val :=
  range_action _ _ _ chi psi (up_action chi psi a b) g x

theorem electronSpace_light (x : ElectronSpace a b) :
    x.val ∈ (mass chi psi a b).radical.toSubmodule := by
  obtain ⟨y, hy⟩ := x.property
  rw [← hy]
  exact electron_light chi psi a b y

theorem electronSpace_action (g : GaugeGroup × H) (x : ElectronSpace a b) :
    (electronLeftRho chi a b g x).val = fieldsRho chi psi g x.val :=
  range_action _ _ _ chi psi (electron_action chi psi a b) g x

def quarkEq : Equiv (quarkRho chi a b) (NeutralQqueExterior.q (charges chi)) :=
  RepresentationConjugation.equiv _ _

def upEq : Equiv (upLeftRho chi a b).dual (NeutralQqueExterior.u (charges chi)) := by
  have eq := SplitRepresentationProjection.dualEquiv
    (RepresentationConjugation.equiv (rangeCoords (upLinear a b) (up_injective a b))
      (StandardSMResidualTensor.charged upRight.dual chi))
  rw [NeutralQqueExterior.charged_dual] at eq
  exact eq.trans (NeutralQqueExterior.chargedEquiv
    (SplitRepresentationProjection.bidualEquiv upRight).symm chi⁻¹)

def electronEq : Equiv (electronLeftRho chi a b).dual (NeutralQqueExterior.e (charges chi)) := by
  have eq := SplitRepresentationProjection.dualEquiv
    (RepresentationConjugation.equiv (rangeCoords (electronLinear a b) (electron_injective a b))
      (StandardSMResidualTensor.charged electronRight.dual chi))
  rw [NeutralQqueExterior.charged_dual] at eq
  exact eq.trans (NeutralQqueExterior.chargedEquiv
    (SplitRepresentationProjection.bidualEquiv electronRight).symm chi⁻¹)

theorem exists_actual_exterior :
    ∃ f : QqueSpinorExterior.ExteriorCoefficient (quarkRho chi a b)
      (upLeftRho chi a b).dual (electronLeftRho chi a b).dual, f ≠ 0 :=
  NeutralQqueExterior.exists_on_fields (charges chi) (neutral chi)
    (quarkRho chi a b) (upLeftRho chi a b).dual (electronLeftRho chi a b).dual
    (quarkEq chi a b) (upEq chi a b) (electronEq chi a b)

theorem exists_light_exterior :
    (∀ x : QuarkSpace a b, x.val ∈ (mass chi psi a b).radical.toSubmodule) ∧
    (∀ x : UpSpace a b, x.val ∈ (mass chi psi a b).radical.toSubmodule) ∧
    (∀ x : ElectronSpace a b, x.val ∈ (mass chi psi a b).radical.toSubmodule) ∧
    ∃ f : QqueSpinorExterior.ExteriorCoefficient (quarkRho chi a b)
      (upLeftRho chi a b).dual (electronLeftRho chi a b).dual, f ≠ 0 :=
  ⟨quarkSpace_light chi psi a b, upSpace_light chi psi a b,
    electronSpace_light chi psi a b, exists_actual_exterior chi a b⟩

theorem mixed_control_exterior :
    ∃ f : QqueSpinorExterior.ExteriorCoefficient
      (quarkRho (1 : PUnit →* Circle) mixedA mixedB)
      (upLeftRho (1 : PUnit →* Circle) mixedA mixedB).dual
      (electronLeftRho (1 : PUnit →* Circle) mixedA mixedB).dual, f ≠ 0 :=
  exists_actual_exterior 1 mixedA mixedB

theorem mixed_control_radical :
    Module.finrank ℂ (mass (1 : PUnit →* Circle) 1 mixedA mixedB).radical.toSubmodule = 15 :=
  active_radical_finrank 1 1 mixedA mixedB mixed_active

theorem partial_control_exterior :
    ∃ f : QqueSpinorExterior.ExteriorCoefficient
      (quarkRho (1 : PUnit →* Circle) unmixedA partialB)
      (upLeftRho (1 : PUnit →* Circle) unmixedA partialB).dual
      (electronLeftRho (1 : PUnit →* Circle) unmixedA partialB).dual, f ≠ 0 :=
  exists_actual_exterior 1 unmixedA partialB

theorem affine_control_exterior :
    ∃ f : QqueSpinorExterior.ExteriorCoefficient
      (quarkRho (1 : PUnit →* Circle) (affineRow 0 1) (affineRow 1 0))
      (upLeftRho (1 : PUnit →* Circle) (affineRow 0 1) (affineRow 1 0)).dual
      (electronLeftRho (1 : PUnit →* Circle) (affineRow 0 1) (affineRow 1 0)).dual, f ≠ 0 :=
  exists_actual_exterior 1 _ _

end
end GUT.SU5.MixedTenMass
