import GUT.SU5.Embeddings.StandardModel
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# The exact global kernel of the standard SU(5) covering homomorphism

The kernel consists precisely of `(z^2 I_3, z^(-3) I_2, z)` with `z^6 = 1`.
The finite quotient, not the covering product, embeds into SU(5).
-/

set_option autoImplicit false

namespace GUT.SU5.StandardModelEmbedding

noncomputable section

open StandardSMGaugeTensor

private theorem circle_smul_eq_one_iff {n : Type*} [Fintype n] [DecidableEq n]
    (z : Circle) (A : Matrix n n ℂ) :
    (z : ℂ) • A = 1 ↔ A = (↑z⁻¹ : ℂ) • (1 : Matrix n n ℂ) := by
  constructor
  · intro h
    calc
      A = (↑z⁻¹ : ℂ) • ((z : ℂ) • A) := by
        rw [smul_smul, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one, one_smul]
      _ = _ := congrArg ((↑z⁻¹ : ℂ) • ·) h
  · intro h
    rw [h, smul_smul, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one, one_smul]

theorem hom_eq_one_iff_scalars (g : GaugeGroup) :
    hom g = 1 ↔
      (g.1 : Matrix (Fin 3) (Fin 3) ℂ) = (↑(g.2.2 ^ (2 : ℕ)) : ℂ) • 1 ∧
      (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ) = (↑(g.2.2 ^ (-3 : ℤ)) : ℂ) • 1 := by
  rw [hom_eq_one_iff_blocks]
  simp only [colorBlock, weakBlock, circle_smul_eq_one_iff, ← zpow_neg, neg_neg]
  rfl

/-- Matrix equations determine the entire kernel, including the sixth-root condition. -/
theorem hom_eq_one_iff (g : GaugeGroup) :
    hom g = 1 ↔ g.2.2 ^ (6 : ℕ) = 1 ∧
      (g.1 : Matrix (Fin 3) (Fin 3) ℂ) = (↑(g.2.2 ^ (2 : ℕ)) : ℂ) • 1 ∧
      (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ) = (↑(g.2.2 ^ (-3 : ℤ)) : ℂ) • 1 := by
  constructor
  · intro h
    obtain ⟨hc, hw⟩ := (hom_eq_one_iff_scalars g).mp h
    refine ⟨?_, hc, hw⟩
    have hd := congrArg Matrix.det hc
    have hdet : Matrix.det (g.1 : Matrix (Fin 3) (Fin 3) ℂ) = 1 := g.1.prop.2
    simp only [hdet, Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one] at hd
    apply Circle.coe_injective
    simpa only [← Circle.coe_pow, ← pow_mul, Circle.coe_one] using hd.symm
  · intro h
    exact (hom_eq_one_iff_scalars g).mpr h.2

/-- A scalar special-unitary matrix, with its determinant condition supplied as a root equation. -/
def scalarSpecialUnitary (n : ℕ) (z : Circle) (hz : z ^ n = 1) :
    Matrix.specialUnitaryGroup (Fin n) ℂ :=
  ⟨(z : ℂ) • 1, circle_smul_unitary z 1 (one_mem _), by
    change Matrix.det ((z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) = 1
    rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one,
      ← Circle.coe_pow, hz, Circle.coe_one]⟩

/-- Every sixth root actually gives an element of the covering-group kernel. -/
def kernelElement (z : Circle) (hz : z ^ (6 : ℕ) = 1) : GaugeGroup :=
  (scalarSpecialUnitary 3 (z ^ (2 : ℕ)) (by simpa only [← pow_mul] using hz),
    scalarSpecialUnitary 2 (z ^ (-3 : ℤ)) (by
      calc
        (z ^ (-3 : ℤ)) ^ (2 : ℕ) = (z ^ (6 : ℕ))⁻¹ := by group
        _ = 1 := by rw [hz, inv_one]), z)

@[simp] theorem kernelElement_phase (z : Circle) (hz : z ^ (6 : ℕ) = 1) :
    (kernelElement z hz).2.2 = z := rfl

@[simp] theorem hom_kernelElement (z : Circle) (hz : z ^ (6 : ℕ) = 1) :
    hom (kernelElement z hz) = 1 :=
  (hom_eq_one_iff _).mpr ⟨hz, rfl, rfl⟩

theorem mem_ker_iff (g : GaugeGroup) :
    g ∈ hom.ker ↔ ∃ (z : Circle) (hz : z ^ (6 : ℕ) = 1), g = kernelElement z hz := by
  constructor
  · intro hg
    obtain ⟨hz, hc, hw⟩ := (hom_eq_one_iff g).mp hg
    refine ⟨g.2.2, hz, ?_⟩
    exact Prod.ext (Subtype.ext hc) (Prod.ext (Subtype.ext hw) rfl)
  · rintro ⟨z, hz, rfl⟩
    exact hom_kernelElement z hz

theorem kernel_phase_injective :
    Function.Injective (fun g : hom.ker => g.val.2.2) := by
  intro g h heq
  obtain ⟨z, hz, hg⟩ := (mem_ker_iff g.val).mp g.prop
  obtain ⟨w, hw, hh⟩ := (mem_ker_iff h.val).mp h.prop
  apply Subtype.ext
  have hzw : z = w := by simpa only [hg, hh, kernelElement_phase] using heq
  subst w
  rw [hg, hh]

/-- Projection to the circle coordinate, with the root equation proved from the matrix kernel. -/
def kernelRootsHom : hom.ker →* rootsOfUnity 6 Circle where
  toFun g := rootsOfUnity.mkOfPowEq g.val.2.2 ((hom_eq_one_iff g.val).mp g.prop).1
  map_one' := rootsOfUnity.coe_injective rfl
  map_mul' _ _ := rootsOfUnity.coe_injective rfl

theorem kernelRootsHom_bijective : Function.Bijective kernelRootsHom := by
  constructor
  · intro g h heq
    exact kernel_phase_injective (congrArg (fun z : rootsOfUnity 6 Circle =>
      (z.val : Circle)) heq)
  · intro z
    have hz : (z.val : Circle) ^ (6 : ℕ) = 1 := (mem_rootsOfUnity' _ _).mp z.prop
    refine ⟨⟨kernelElement (z.val : Circle) hz, hom_kernelElement _ hz⟩, ?_⟩
    exact rootsOfUnity.coe_injective rfl

def kernelRootsEquiv : hom.ker ≃* rootsOfUnity 6 Circle :=
  MulEquiv.ofBijective kernelRootsHom kernelRootsHom_bijective

/-- The cyclic parameter uses the standard exponential character on `ZMod 6`. -/
def cyclicRootsEquiv : Multiplicative (ZMod 6) ≃* rootsOfUnity 6 Circle :=
  MulEquiv.ofBijective (ZMod.rootsOfUnityAddChar 6).toMonoidHom
    (bijective_rootsOfUnityAddChar 6)

def kernelCyclicEquiv : hom.ker ≃* Multiplicative (ZMod 6) :=
  kernelRootsEquiv.trans cyclicRootsEquiv.symm

theorem kernel_card : Nat.card hom.ker = 6 := by
  rw [Nat.card_congr kernelCyclicEquiv.toEquiv]
  simp

instance kernel_isCyclic : IsCyclic hom.ker :=
  isCyclic_of_injective kernelCyclicEquiv.toMonoidHom kernelCyclicEquiv.injective

theorem kernel_le_center : hom.ker ≤ Subgroup.center GaugeGroup := by
  intro g hg
  obtain ⟨z, hz, rfl⟩ := (mem_ker_iff g).mp hg
  rw [Subgroup.mem_center_iff]
  intro h
  apply Prod.ext
  · apply Subtype.ext
    change (h.1 : Matrix (Fin 3) (Fin 3) ℂ) * ((↑(z ^ (2 : ℕ)) : ℂ) • 1) =
      ((↑(z ^ (2 : ℕ)) : ℂ) • 1) * (h.1 : Matrix (Fin 3) (Fin 3) ℂ)
    simp
  · apply Prod.ext
    · apply Subtype.ext
      change (h.2.1 : Matrix (Fin 2) (Fin 2) ℂ) * ((↑(z ^ (-3 : ℤ)) : ℂ) • 1) =
        ((↑(z ^ (-3 : ℤ)) : ℂ) • 1) * (h.2.1 : Matrix (Fin 2) (Fin 2) ℂ)
      simp
    · exact mul_comm _ _

/-- The element `(I_3, -I_2, -1)` is a concrete nonidentity element of the kernel. -/
def signKernelElement : GaugeGroup := kernelElement (-1) (by norm_num)

@[simp] theorem hom_signKernelElement : hom signKernelElement = 1 :=
  hom_kernelElement _ _

theorem signKernelElement_ne_one : signKernelElement ≠ 1 := by
  intro h
  have heq : (-1 : Circle) = 1 := congrArg (fun g : GaugeGroup => g.2.2) h
  have hc := congrArg ((↑) : Circle → ℂ) heq
  norm_num at hc

theorem hom_not_injective : ¬ Function.Injective hom := by
  intro h
  exact signKernelElement_ne_one (h (hom_signKernelElement.trans (map_one hom).symm))

end

end GUT.SU5.StandardModelEmbedding
