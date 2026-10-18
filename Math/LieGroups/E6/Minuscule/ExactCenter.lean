import Math.LieGroups.E6.Minuscule.CubicGroupInvariant
import Math.LieGroups.E6.Minuscule.CenterThree

/-! The actual connected compact candidate has center of order three.
This does not assert simple connectedness or global E6 identification. -/

set_option autoImplicit false

namespace Math.E6.Minuscule

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

theorem compact_scalar_cube (g : compactIdentityComponent) (z : ℂ)
    (hz : compactMatrix g = z • (1 : Matrix27)) : z ^ 3 = 1 := by
  have h := cubic_invariant g cubicWitness
  rw [hz, Matrix.smul_mulVec, Matrix.one_mulVec, cubic_homogeneous, cubic_witness, mul_one] at h
  exact h

theorem compactCenterScalar_cube (g : Subgroup.center compactIdentityComponent) :
    compactCenterScalar g ^ 3 = 1 :=
  compact_scalar_cube g.val _ (compact_center_scalar g.val g.property)

def compactCenterCubeRoot : Subgroup.center compactIdentityComponent →* rootsOfUnity 3 ℂ where
  toFun g := ⟨Units.mk0 (compactCenterScalar g) (compactCenterScalar_ne_zero g),
    (mem_rootsOfUnity' 3 _).mpr (compactCenterScalar_cube g)⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    exact compactCenterScalar.map_one
  map_mul' g h := by
    apply Subtype.ext
    apply Units.ext
    exact compactCenterScalar.map_mul g h

theorem compactCenterCubeRoot_injective : Function.Injective compactCenterCubeRoot := by
  intro g h he
  apply compactCenterScalar_injective
  exact congrArg (fun z : rootsOfUnity 3 ℂ => ((z : ℂˣ) : ℂ)) he

theorem compactCenter_card : Nat.card (Subgroup.center compactIdentityComponent) = 3 := by
  apply Nat.dvd_antisymm _ three_dvd_compactCenter_card
  simpa only [Complex.card_rootsOfUnity] using
    Subgroup.card_dvd_of_injective compactCenterCubeRoot compactCenterCubeRoot_injective

def compactCenterEquivCubeRoots : Subgroup.center compactIdentityComponent ≃* rootsOfUnity 3 ℂ :=
  MulEquiv.ofBijective compactCenterCubeRoot
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨compactCenterCubeRoot_injective, by rw [compactCenter_card, Complex.card_rootsOfUnity]⟩)

theorem compact_center_cube (g : compactIdentityComponent)
    (hg : g ∈ Subgroup.center compactIdentityComponent) : g ^ 3 = 1 := by
  have he : (⟨g, hg⟩ : Subgroup.center compactIdentityComponent) ^ 3 = 1 := by
    apply compactCenterScalar_injective
    rw [map_pow, map_one]
    exact compactCenterScalar_cube _
  exact congrArg Subtype.val he

theorem centralScalar27_not_mem : centralScalar27 ∉ compactIdentityComponent := by
  intro hm
  have hc : (⟨centralScalar27, hm⟩ : compactIdentityComponent) ∈
      Subgroup.center compactIdentityComponent := by
    apply (compact_mem_center_iff_scalar _).mpr
    refine ⟨scalarRoot27, ?_⟩
    simpa [compactMatrix] using centralScalar27_pow_coe 1
  have he := congrArg Subtype.val (compact_center_cube _ hc)
  have hd := (centralScalar27_pow_eq_one_iff 3).mp he
  norm_num at hd

end

end Math.E6.Minuscule
