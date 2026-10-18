import GUT.SU5.SelectionRules.MixedTenMass

/-! Arbitrary species matrices on finite copies of actual SU(5) tens. -/
namespace GUT.SU5.MatrixTenMass
set_option autoImplicit false
noncomputable section
open Math Representation StandardModelEmbedding Matter ExteriorSquareBranching
open StandardSMGaugeTensor SMEpsilonTensor InvariantWeylMass
open MixedTenMass
local instance : AddCommGroup Quark := inferInstance
local instance : AddCommGroup Ten := inferInstance
variable {H : Type*} [CommGroup H] {p q : ℕ}

structure Matrices (p q : ℕ) where
  up : Matrix (Fin q) (Fin p) ℂ
  quark : Matrix (Fin q) (Fin p) ℂ
  electron : Matrix (Fin q) (Fin p) ℂ

def row (A : Matrices p q) (j : Fin q) (i : Fin p) : RowWeights :=
  ⟨A.up j i, A.quark j i, A.electron j i⟩

def copies (n : ℕ) (rho : Representation ℂ (GaugeGroup × H) Ten) :
    Representation ℂ (GaugeGroup × H) (Fin n → Ten) where
  toFun g := LinearMap.pi fun i => (rho g).comp (LinearMap.proj i)
  map_one' := by ext x i; simp
  map_mul' g h := by ext x i; simp [map_mul]

abbrev Source (p : ℕ) := (Fin p → Ten) × BarFive
abbrev Target (q : ℕ) := Fin q → Ten
abbrev Fields (p q : ℕ) := Source p × Module.Dual ℂ (Target q)

def sourceRho (chi psi : H →* Circle) (p : ℕ) :=
  (copies p (tenRho chi)).prod (barRho psi)
def targetRho (chi : H →* Circle) (q : ℕ) := copies q (tenRho chi)
def fieldsRho (chi psi : H →* Circle) (p q : ℕ) :=
  (sourceRho chi psi p).prod (targetRho chi q).dual

def massMap (chi psi : H →* Circle) (A : Matrices p q) :
    IntertwiningMap (sourceRho chi psi p) (targetRho chi q) where
  toLinearMap := {
    toFun := fun x j => ∑ i, weighted (row A j i) (x.1 i)
    map_add' := by intro x y; funext j; simp [map_add, Finset.sum_add_distrib]
    map_smul' := by intro z x; funext j; simp [map_smul, Finset.smul_sum] }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    funext j
    change (∑ i, weighted (row A j i) (tenRho chi g (x.1 i))) =
      tenRho chi g (∑ i, weighted (row A j i) (x.1 i))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (chargedWeighted chi (row A j i)).isIntertwining _ _ g (x.1 i)

def mass (chi psi : H →* Circle) (A : Matrices p q) := ofDirac (massMap chi psi A)

theorem mem_radical_iff (chi psi : H →* Circle) (A : Matrices p q) (x : Fields p q) :
    x ∈ (mass chi psi A).radical.toSubmodule ↔
      massMap chi psi A x.1 = 0 ∧ ∀ v, x.2 (massMap chi psi A v) = 0 :=
  DiracWeylConvention.mem_radical_iff _ _

def matrixMap (M : Matrix (Fin q) (Fin p) ℂ) :
    (Fin p → ℂ) →ₗ[ℂ] (Fin q → ℂ) := Matrix.toLin' M

theorem kernel_dimension (M : Matrix (Fin q) (Fin p) ℂ) :
    p ≤ q + Module.finrank ℂ (LinearMap.ker (matrixMap M)) := by
  have hn := LinearMap.finrank_range_add_finrank_ker (matrixMap M)
  have hr := Submodule.finrank_le (LinearMap.range (matrixMap M))
  simp only [Module.finrank_pi, Fintype.card_fin] at hn hr
  omega

theorem exists_kernel_vector (M : Matrix (Fin q) (Fin p) ℂ) (h : q < p) :
    ∃ v : Fin p → ℂ, v ≠ 0 ∧ matrixMap M v = 0 := by
  have hp : 0 < Module.finrank ℂ (LinearMap.ker (matrixMap M)) := by
    have := kernel_dimension M
    omega
  let : Nontrivial (LinearMap.ker (matrixMap M)) := Module.nontrivial_of_finrank_pos hp
  obtain ⟨v, hv⟩ := exists_ne (0 : LinearMap.ker (matrixMap M))
  refine ⟨v.val, ?_, v.property⟩
  intro hz
  apply hv
  exact Subtype.ext hz

structure Kernels (A : Matrices p q) where
  up : Fin p → ℂ
  quark : Fin p → ℂ
  electron : Fin p → ℂ
  up_ne : up ≠ 0
  quark_ne : quark ≠ 0
  electron_ne : electron ≠ 0
  up_zero : matrixMap A.up up = 0
  quark_zero : matrixMap A.quark quark = 0
  electron_zero : matrixMap A.electron electron = 0

def kernels (A : Matrices p q) (h : q < p) : Kernels A :=
  let u := Classical.choose (exists_kernel_vector A.up h)
  let v := Classical.choose (exists_kernel_vector A.quark h)
  let e := Classical.choose (exists_kernel_vector A.electron h)
  ⟨u, v, e, (Classical.choose_spec (exists_kernel_vector A.up h)).1,
    (Classical.choose_spec (exists_kernel_vector A.quark h)).1,
    (Classical.choose_spec (exists_kernel_vector A.electron h)).1,
    (Classical.choose_spec (exists_kernel_vector A.up h)).2,
    (Classical.choose_spec (exists_kernel_vector A.quark h)).2,
    (Classical.choose_spec (exists_kernel_vector A.electron h)).2⟩

def lightMap {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : V →ₗ[ℂ] Ten) (v : Fin p → ℂ) : V →ₗ[ℂ] Fields p q where
  toFun x := ((fun i => v i • f x, 0), 0)
  map_add' x y := by ext i <;> simp [map_add, smul_add]
  map_smul' z x := by ext i <;> simp [map_smul, smul_smul, mul_comm]

theorem lightMap_injective {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : V →ₗ[ℂ] Ten) (hf : Function.Injective f) (v : Fin p → ℂ) (hv : v ≠ 0) :
    Function.Injective (lightMap (q := q) f v) := by
  have hex : ∃ i, v i ≠ 0 := by
    by_contra hn
    apply hv
    ext i
    simpa using (not_exists.mp hn i)
  obtain ⟨i, hi⟩ := hex
  intro x y he
  apply hf
  exact (smul_right_injective _ hi) (congrArg (fun z : Fields p q => z.1.1 i) he)

variable (chi psi : H →* Circle) (A : Matrices p q) (K : Kernels A)

def quarkLinear := lightMap (q := q) quarkTen K.quark

theorem quark_injective : Function.Injective (quarkLinear A K) :=
  lightMap_injective quarkTen quarkTen_injective K.quark K.quark_ne

theorem quark_light (x : Quark) :
    quarkLinear A K x ∈ (mass chi psi A).radical.toSubmodule := by
  rw [mem_radical_iff]
  constructor
  · funext j
    change (∑ i, weighted (row A j i) (K.quark i • quarkTen x)) = 0
    simp_rw [map_smul, quark_weighted, smul_smul]
    change (∑ i, (K.quark i * A.quark j i) • quarkTen x) = 0
    rw [← Finset.sum_smul]
    have he := congrFun K.quark_zero j
    change (∑ i, A.quark j i * K.quark i) = 0 at he
    simp_rw [mul_comm (K.quark _) _]
    rw [he, zero_smul]
  · intro v; rfl

theorem quark_action (g : GaugeGroup × H) (x : Quark) :
    fieldsRho chi psi p q g (quarkLinear A K x) =
      quarkLinear A K (StandardSMResidualTensor.charged quark chi g x) := by
  apply Prod.ext
  · apply Prod.ext
    · funext i
      change (chi g.2 : ℂ) • ten (hom g.1) (K.quark i • quarkTen x) =
        K.quark i • quarkTen ((chi g.2 : ℂ) • quark g.1 x)
      simp [map_smul, quarkTen_action, smul_smul, mul_comm]
    · change barRho psi g 0 = 0
      exact map_zero _
  · change (targetRho chi q).dual g 0 = 0
    exact map_zero _

def upLinear := lightMap (q := q) upTen K.up

theorem up_injective : Function.Injective (upLinear A K) :=
  lightMap_injective upTen upTen_injective K.up K.up_ne

theorem up_light (x : Module.Dual ℂ Color) :
    upLinear A K x ∈ (mass chi psi A).radical.toSubmodule := by
  rw [mem_radical_iff]
  constructor
  · funext j
    change (∑ i, weighted (row A j i) (K.up i • upTen x)) = 0
    simp_rw [map_smul, up_weighted, smul_smul]
    change (∑ i, (K.up i * A.up j i) • upTen x) = 0
    rw [← Finset.sum_smul]
    have he := congrFun K.up_zero j
    change (∑ i, A.up j i * K.up i) = 0 at he
    simp_rw [mul_comm (K.up _) _]
    rw [he, zero_smul]
  · intro v; rfl

theorem up_action (g : GaugeGroup × H) (x : Module.Dual ℂ Color) :
    fieldsRho chi psi p q g (upLinear A K x) =
      upLinear A K (StandardSMResidualTensor.charged upRight.dual chi g x) := by
  apply Prod.ext
  · apply Prod.ext
    · funext i
      change (chi g.2 : ℂ) • ten (hom g.1) (K.up i • upTen x) =
        K.up i • upTen ((chi g.2 : ℂ) • upRight.dual g.1 x)
      simp [map_smul, upTen_action, smul_smul, mul_comm]
    · change barRho psi g 0 = 0
      exact map_zero _
  · change (targetRho chi q).dual g 0 = 0
    exact map_zero _

def electronLinear := lightMap (q := q) electronTen K.electron

theorem electron_injective : Function.Injective (electronLinear A K) :=
  lightMap_injective electronTen electronTen_injective K.electron K.electron_ne

theorem electron_light (x : Module.Dual ℂ ℂ) :
    electronLinear A K x ∈ (mass chi psi A).radical.toSubmodule := by
  rw [mem_radical_iff]
  constructor
  · funext j
    change (∑ i, weighted (row A j i) (K.electron i • electronTen x)) = 0
    simp_rw [map_smul, electron_weighted, smul_smul]
    change (∑ i, (K.electron i * A.electron j i) • electronTen x) = 0
    rw [← Finset.sum_smul]
    have he := congrFun K.electron_zero j
    change (∑ i, A.electron j i * K.electron i) = 0 at he
    simp_rw [mul_comm (K.electron _) _]
    rw [he, zero_smul]
  · intro v; rfl

theorem electron_action (g : GaugeGroup × H) (x : Module.Dual ℂ ℂ) :
    fieldsRho chi psi p q g (electronLinear A K x) =
      electronLinear A K (StandardSMResidualTensor.charged electronRight.dual chi g x) := by
  apply Prod.ext
  · apply Prod.ext
    · funext i
      change (chi g.2 : ℂ) • ten (hom g.1) (K.electron i • electronTen x) =
        K.electron i • electronTen ((chi g.2 : ℂ) • electronRight.dual g.1 x)
      simp [map_smul, electronTen_action, smul_smul, mul_comm]
    · change barRho psi g 0 = 0
      exact map_zero _
  · change (targetRho chi q).dual g 0 = 0
    exact map_zero _
section RangeTransport
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def rangeCoords (f : V →ₗ[ℂ] Fields p q) (hf : Function.Injective f) :
    LinearMap.range f ≃ₗ[ℂ] V := (LinearEquiv.ofInjective f hf).symm

def rangeRho (f : V →ₗ[ℂ] Fields p q) (hf : Function.Injective f)
    (rho : Representation ℂ (GaugeGroup × H) V) :=
  RepresentationConjugation.pullback (rangeCoords f hf) rho

theorem range_coords (f : V →ₗ[ℂ] Fields p q) (hf : Function.Injective f)
    (x : LinearMap.range f) : f (rangeCoords f hf x) = x.val :=
  congrArg Subtype.val ((rangeCoords f hf).symm_apply_apply x)

theorem range_action (f : V →ₗ[ℂ] Fields p q) (hf : Function.Injective f)
    (rho : Representation ℂ (GaugeGroup × H) V) (chi psi : H →* Circle)
    (he : ∀ g x, fieldsRho chi psi p q g (f x) = f (rho g x))
    (g : GaugeGroup × H) (x : LinearMap.range f) :
    (rangeRho f hf rho g x).val = fieldsRho chi psi p q g x.val := by
  rw [rangeRho, RepresentationConjugation.pullback_apply]
  change f (rho g (rangeCoords f hf x)) = _
  rw [← he, range_coords]

end RangeTransport


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

abbrev QuarkSpace := LinearMap.range (quarkLinear A K)
abbrev UpSpace := LinearMap.range (upLinear A K)
abbrev ElectronSpace := LinearMap.range (electronLinear A K)

local instance : AddCommGroup (QuarkSpace A K) := inferInstance
local instance : AddCommGroup (UpSpace A K) := inferInstance
local instance : AddCommGroup (ElectronSpace A K) := inferInstance

def quarkRho := rangeRho (quarkLinear A K) (quark_injective A K)
  (StandardSMResidualTensor.charged quark chi)
def upLeftRho := rangeRho (upLinear A K) (up_injective A K)
  (StandardSMResidualTensor.charged upRight.dual chi)
def electronLeftRho := rangeRho (electronLinear A K) (electron_injective A K)
  (StandardSMResidualTensor.charged electronRight.dual chi)

theorem quarkSpace_light (x : QuarkSpace A K) :
    x.val ∈ (mass chi psi A).radical.toSubmodule := by
  obtain ⟨y, hy⟩ := x.property
  rw [← hy]
  exact quark_light chi psi A K y

theorem quarkSpace_action (g : GaugeGroup × H) (x : QuarkSpace A K) :
    (quarkRho chi A K g x).val = fieldsRho chi psi p q g x.val :=
  range_action _ _ _ chi psi (quark_action chi psi A K) g x

theorem upSpace_light (x : UpSpace A K) :
    x.val ∈ (mass chi psi A).radical.toSubmodule := by
  obtain ⟨y, hy⟩ := x.property
  rw [← hy]
  exact up_light chi psi A K y

theorem upSpace_action (g : GaugeGroup × H) (x : UpSpace A K) :
    (upLeftRho chi A K g x).val = fieldsRho chi psi p q g x.val :=
  range_action _ _ _ chi psi (up_action chi psi A K) g x

theorem electronSpace_light (x : ElectronSpace A K) :
    x.val ∈ (mass chi psi A).radical.toSubmodule := by
  obtain ⟨y, hy⟩ := x.property
  rw [← hy]
  exact electron_light chi psi A K y

theorem electronSpace_action (g : GaugeGroup × H) (x : ElectronSpace A K) :
    (electronLeftRho chi A K g x).val = fieldsRho chi psi p q g x.val :=
  range_action _ _ _ chi psi (electron_action chi psi A K) g x

def quarkEq : Equiv (quarkRho chi A K) (NeutralQqueExterior.q (charges chi)) :=
  RepresentationConjugation.equiv _ _

def upEq : Equiv (upLeftRho chi A K).dual (NeutralQqueExterior.u (charges chi)) := by
  have eq := SplitRepresentationProjection.dualEquiv
    (RepresentationConjugation.equiv (rangeCoords (upLinear A K) (up_injective A K))
      (StandardSMResidualTensor.charged upRight.dual chi))
  rw [NeutralQqueExterior.charged_dual] at eq
  exact eq.trans (NeutralQqueExterior.chargedEquiv
    (SplitRepresentationProjection.bidualEquiv upRight).symm chi⁻¹)

def electronEq : Equiv (electronLeftRho chi A K).dual (NeutralQqueExterior.e (charges chi)) := by
  have eq := SplitRepresentationProjection.dualEquiv
    (RepresentationConjugation.equiv (rangeCoords (electronLinear A K) (electron_injective A K))
      (StandardSMResidualTensor.charged electronRight.dual chi))
  rw [NeutralQqueExterior.charged_dual] at eq
  exact eq.trans (NeutralQqueExterior.chargedEquiv
    (SplitRepresentationProjection.bidualEquiv electronRight).symm chi⁻¹)

theorem exists_actual_exterior :
    ∃ f : QqueSpinorExterior.ExteriorCoefficient (quarkRho chi A K)
      (upLeftRho chi A K).dual (electronLeftRho chi A K).dual, f ≠ 0 :=
  NeutralQqueExterior.exists_on_fields (charges chi) (neutral chi)
    (quarkRho chi A K) (upLeftRho chi A K).dual (electronLeftRho chi A K).dual
    (quarkEq chi A K) (upEq chi A K) (electronEq chi A K)

theorem exists_light_exterior :
    (∀ x : QuarkSpace A K, x.val ∈ (mass chi psi A).radical.toSubmodule) ∧
    (∀ x : UpSpace A K, x.val ∈ (mass chi psi A).radical.toSubmodule) ∧
    (∀ x : ElectronSpace A K, x.val ∈ (mass chi psi A).radical.toSubmodule) ∧
    ∃ f : QqueSpinorExterior.ExteriorCoefficient (quarkRho chi A K)
      (upLeftRho chi A K).dual (electronLeftRho chi A K).dual, f ≠ 0 :=
  ⟨quarkSpace_light chi psi A K, upSpace_light chi psi A K,
    electronSpace_light chi psi A K, exists_actual_exterior chi A K⟩


/-- Every rectangular species matrix with more source than target copies
has actual light species supporting a nonzero physical exterior coefficient. -/
theorem rectangular_light_exterior (h : q < p) :
    (∀ x : QuarkSpace A (kernels A h), x.val ∈ (mass chi psi A).radical.toSubmodule) ∧
    (∀ x : UpSpace A (kernels A h), x.val ∈ (mass chi psi A).radical.toSubmodule) ∧
    (∀ x : ElectronSpace A (kernels A h), x.val ∈ (mass chi psi A).radical.toSubmodule) ∧
    ∃ f : QqueSpinorExterior.ExteriorCoefficient (quarkRho chi A (kernels A h))
      (upLeftRho chi A (kernels A h)).dual
      (electronLeftRho chi A (kernels A h)).dual, f ≠ 0 :=
  exists_light_exterior chi psi A (kernels A h)

end
end GUT.SU5.MatrixTenMass
