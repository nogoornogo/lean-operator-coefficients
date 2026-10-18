import Physics.FieldTheory.Mass.FlavorMajoranaLine
import Math.RepresentationTheory.Decomposition.SurjectiveHomTransport

open Math

/-! Diagonal Majorana coefficients within the independent-phase candidate
group. This is not a classification of the full unitary mixing stabilizer. -/
namespace GUT.FlavorMajoranaDiagonal
set_option autoImplicit false
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

def phaseAction : Representation ℂ (I → Circle) (I → ℂ) where
  toFun z :=
    { toFun := fun x i => (z i : ℂ) * x i
      map_add' := by intros; ext i; simp [mul_add]
      map_smul' := by intros; ext i; simp [mul_left_comm] }
  map_one' := by apply LinearMap.ext; intro x; ext i; simp
  map_mul' z w := by
    apply LinearMap.ext; intro x; ext i
    simp [Circle.coe_mul, mul_assoc]

def form (c : I → ℂ) : LinearMap.BilinForm ℂ (I → ℂ) :=
  ∑ i, (FlavorMajoranaLine.form (c i)).compl₁₂ (LinearMap.proj i) (LinearMap.proj i)

omit [DecidableEq I] in
@[simp] theorem form_apply (c x y : I → ℂ) :
    form c x y = ∑ i, c i * (x i * y i) := by
  simp [form, FlavorMajoranaLine.form]

omit [DecidableEq I] in
theorem form_symmetric (c : I → ℂ) : (form c).IsSymm := by
  constructor
  intro x y
  simp only [form_apply, mul_comm (x _) (y _)]

def subgroup (c : I → ℂ) : Subgroup (I → Circle) :=
  FlavorStabilizer.massSubgroup phaseAction (form c)

theorem mem_iff (c : I → ℂ) (z : I → Circle) :
    z ∈ subgroup c ↔ ∀ i, z i ∈ FlavorMajoranaLine.subgroup (c i) := by
  rw [subgroup, FlavorStabilizer.mass_mem_iff]
  constructor
  · intro h i
    rw [FlavorMajoranaLine.subgroup, FlavorStabilizer.mass_mem_iff]
    intro x y
    have hi := h (Pi.single i x) (Pi.single i y)
    simpa [form_apply, phaseAction, FlavorMajoranaLine.phaseAction,
      FlavorMajoranaLine.form, Pi.single_apply] using hi
  · intro h x y
    simp only [form_apply]
    apply Finset.sum_congr rfl
    intro i hi
    exact (FlavorStabilizer.mass_mem_iff _ _ _).mp (h i) (x i) (y i)

theorem membership (c : I → ℂ) (z : I → Circle) :
    z ∈ subgroup c ↔ ∀ i, c i = 0 ∨ z i ^ 2 = 1 := by
  simp only [mem_iff, FlavorMajoranaLine.mem_iff]

def productEquiv (c : I → ℂ) :
    subgroup c ≃* (∀ i, FlavorMajoranaLine.subgroup (c i)) where
  toFun z i := ⟨z.val i, (mem_iff c z.val).mp z.property i⟩
  invFun z := ⟨fun i => (z i).val, (mem_iff c _).mpr (fun i => (z i).property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem zero_subgroup : subgroup (fun _ : I => 0) = ⊤ := by
  ext z
  simp [membership]

def nonzeroEquiv (c : I → ℂ) (hc : ∀ i, c i ≠ 0) :
    subgroup c ≃* (I → Multiplicative (ZMod 2)) :=
  (productEquiv c).trans (MulEquiv.piCongrRight fun i => FlavorMajoranaLine.cyclicEquiv (c i) (hc i))

theorem nonzero_card (c : I → ℂ) (hc : ∀ i, c i ≠ 0) :
    Nat.card (subgroup c) = 2 ^ Fintype.card I := by
  rw [Nat.card_congr (nonzeroEquiv c hc).toEquiv]
  simp [Nat.card_eq_fintype_card]

/-- A zero coordinate contributes an unrestricted Circle factor. Nonzero
coordinates use `FlavorMajoranaLine.cyclicEquiv`. -/
def zeroFactorEquiv (c : ℂ) (hc : c = 0) : FlavorMajoranaLine.subgroup c ≃* Circle := by
  subst c
  exact
    { toFun := fun z => z.val
      invFun := fun z => ⟨z, (FlavorMajoranaLine.mem_iff 0 z).mpr (Or.inl rfl)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }

/-- Mixed support has one Circle for each zero coefficient and one sign
factor for each nonzero coefficient; both directions are explicit. -/
def mixedEquiv (c : I → ℂ) : subgroup c ≃*
    (({i : I // c i = 0} → Circle) ×
      ({i : I // c i ≠ 0} → Multiplicative (ZMod 2))) := by
  classical
  let e := productEquiv c
  let f : (∀ i, FlavorMajoranaLine.subgroup (c i)) ≃*
      (({i : I // c i = 0} → Circle) ×
        ({i : I // c i ≠ 0} → Multiplicative (ZMod 2))) :=
    { toFun := fun z =>
        (fun i => zeroFactorEquiv (c i.val) i.property (z i.val),
         fun i => FlavorMajoranaLine.cyclicEquiv (c i.val) i.property (z i.val))
      invFun := fun z i => if hc : c i = 0 then
          (zeroFactorEquiv (c i) hc).symm (z.1 ⟨i, hc⟩)
        else (FlavorMajoranaLine.cyclicEquiv (c i) hc).symm (z.2 ⟨i, hc⟩)
      left_inv := by
        intro z; funext i
        by_cases hc : c i = 0 <;> simp [hc]
      right_inv := by
        intro z
        apply Prod.ext
        · funext i; simp [i.property]
        · funext i; simp [i.property]
      map_mul' := by
        intro z w
        apply Prod.ext
        · funext i; exact (zeroFactorEquiv (c i.val) i.property).map_mul _ _
        · funext i; exact (FlavorMajoranaLine.cyclicEquiv (c i.val) i.property).map_mul _ _ }
  exact e.trans f

theorem evaluation_le (c v : I → ℂ) :
    subgroup c ≤ subgroup (fun i => c i * v i) := by
  intro z hz
  rw [membership] at hz ⊢
  intro i
  rcases hz i with h | h
  · exact Or.inl (by rw [h, zero_mul])
  · exact Or.inr h

theorem evaluation_eq (c v : I → ℂ) (hv : ∀ i, c i ≠ 0 → v i ≠ 0) :
    subgroup (fun i => c i * v i) = subgroup c := by
  ext z
  simp only [membership, mul_eq_zero]
  constructor
  · intro h i
    rcases h i with (h | h) | h
    · exact Or.inl h
    · by_cases hc : c i = 0
      · exact Or.inl hc
      · exact False.elim (hv i hc h)
    · exact Or.inr h
  · intro h i
    rcases h i with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h

theorem evaluation_eq_iff (c v : I → ℂ) :
    subgroup (fun i => c i * v i) = subgroup c ↔ ∀ i, c i ≠ 0 → v i ≠ 0 := by
  constructor
  · intro heq i hc hv
    let z : I → Circle := fun j => if j = i then Circle.exp (Real.pi / 2) else 1
    have hz : z ∈ subgroup (fun j => c j * v j) := by
      rw [membership]
      intro j
      by_cases hj : j = i
      · subst j; exact Or.inl (by rw [hv, mul_zero])
      · exact Or.inr (by simp [z, hj])
    rw [heq, membership] at hz
    have hi := (hz i).resolve_left hc
    simp only [z, ite_eq_left rfl] at hi
    have he : Circle.exp (Real.pi / 2) ^ 2 = Circle.exp Real.pi := by
      rw [← Circle.exp_natCast_mul]
      congr 1
      ring
    rw [he] at hi
    exact Circle.exp_pi_ne_one hi
  · exact evaluation_eq c v

/-- Neutral scalar coordinates evaluate to the diagonal mass coefficients. -/
def coupling (c : I → ℂ) : (I → ℂ) →ₗ[ℂ] LinearMap.BilinForm ℂ (I → ℂ) :=
  ∑ i, (LinearMap.toSpanSingleton ℂ _
    ((FlavorMajoranaLine.form (c i)).compl₁₂ (LinearMap.proj i) (LinearMap.proj i))).comp
      (LinearMap.proj i)

omit [DecidableEq I] in
theorem coupling_evaluation (c v : I → ℂ) : coupling c v = form (fun i => c i * v i) := by
  apply LinearMap.ext; intro x
  apply LinearMap.ext; intro y
  simp only [coupling, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply, LinearMap.proj_apply, LinearMap.smul_apply,
    smul_eq_mul, LinearMap.compl₁₂_apply, FlavorMajoranaLine.form, form_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change v i * (c i * (x i * y i)) = c i * v i * (x i * y i)
  ring

theorem coupling_subgroup (c : I → ℂ) :
    FlavorStabilizer.couplingSubgroup
      (Representation.trivial ℂ (I → Circle) (I → ℂ)) phaseAction (coupling c) =
        subgroup c := by
  ext z
  rw [FlavorStabilizer.coupling_mem_iff]
  constructor
  · intro h
    rw [subgroup, FlavorStabilizer.mass_mem_iff]
    intro x y
    have he := h (fun _ => 1) x y
    change coupling c (fun _ => 1) (phaseAction z x) (phaseAction z y) =
      coupling c (fun _ => 1) x y at he
    simpa only [coupling_evaluation, mul_one] using he
  · intro hz v x y
    change coupling c v (phaseAction z x) (phaseAction z y) = coupling c v x y
    rw [coupling_evaluation]
    exact (FlavorStabilizer.mass_mem_iff _ _ _).mp (evaluation_le c v hz) x y

/-- Hom classification is unchanged by the explicit residual-group coordinates. -/
def residualHomEquiv {U W : Type*} [AddCommMonoid U] [Module ℂ U]
    [AddCommMonoid W] [Module ℂ W] (c : I → ℂ)
    (a : Representation ℂ (subgroup c) U) (b : Representation ℂ (subgroup c) W) :
    Representation.IntertwiningMap
      (a.comp (mixedEquiv c).symm.toMonoidHom)
      (b.comp (mixedEquiv c).symm.toMonoidHom) ≃ₗ[ℂ]
      Representation.IntertwiningMap a b :=
  SurjectiveHomTransport.homEquiv (mixedEquiv c).symm.toMonoidHom
    (mixedEquiv c).symm.surjective a b

theorem residual_nonzero_iff {U W : Type*} [AddCommMonoid U] [Module ℂ U]
    [AddCommMonoid W] [Module ℂ W] (c : I → ℂ)
    (a : Representation ℂ (subgroup c) U) (b : Representation ℂ (subgroup c) W) :
    (∃ f : Representation.IntertwiningMap
      (a.comp (mixedEquiv c).symm.toMonoidHom)
      (b.comp (mixedEquiv c).symm.toMonoidHom), f ≠ 0) ↔
        ∃ f : Representation.IntertwiningMap a b, f ≠ 0 :=
  SurjectiveHomTransport.nonzero_iff (mixedEquiv c).symm.toMonoidHom
    (mixedEquiv c).symm.surjective a b

end
end GUT.FlavorMajoranaDiagonal
