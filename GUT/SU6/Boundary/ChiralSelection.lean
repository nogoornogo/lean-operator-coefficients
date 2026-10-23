import Math.LinearAlgebra.Boundary.Projectors
import GUT.SU6.Boundary.ExteriorCube

/-! The unmixed chiral boundary amplitudes of arXiv:2104.07366v2,
(5)--(8), with color-first repository coordinates. A plus sign means that
component is retained. Right chirality uses both complementary projectors. -/
namespace GUT.SU6BoundarySelection
set_option autoImplicit false
noncomputable section
open Math Physics StandardSMGaugeTensor SMEpsilonTensor StandardSMExterior

abbrev Light15 := Quark × Module.Dual ℂ ℂ

def uv15 : Blocks →ₗ[ℂ] Blocks where
  toFun x := (x.1, (x.2.1, (x.2.2.1, (0,0))))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def ir15 : Blocks →ₗ[ℂ] Blocks where
  toFun x := (0, x.2)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def fifteen : BoundaryProjectors.Pair (K := ℂ) (V := Blocks) where
  uv := uv15
  ir := ir15
  uv_idem := by ext x <;> rfl
  ir_idem := by ext x <;> rfl
  commute := by ext x <;> rfl

def embed15 : Light15 →ₗ[ℂ] Blocks where
  toFun x := (0, (x.1, (x.2, (0,0))))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def extract15 : Blocks →ₗ[ℂ] Light15 :=
  (LinearMap.fst ℂ Quark _).comp (LinearMap.snd ℂ _ _) |>.prod
    ((LinearMap.fst ℂ (Module.Dual ℂ ℂ) _).comp
      ((LinearMap.snd ℂ Quark _).comp (LinearMap.snd ℂ _ _)))

@[simp] theorem extract_embed15 (x : Light15) : extract15 (embed15 x) = x := rfl

theorem left15_exact (x : Blocks) :
    x ∈ fifteen.selected ↔ embed15 (extract15 x) = x := by
  rw [BoundaryProjectors.Pair.mem_selected]
  constructor
  · rintro ⟨hu, hi⟩
    change (x.1, (x.2.1, (x.2.2.1, (0,0)))) = x at hu
    change (0, x.2) = x at hi
    have h := congrArg Prod.fst hi
    have ht := congrArg (fun z : Blocks => z.2.2.2) hu
    change (0, (x.2.1, (x.2.2.1, (0,0)))) = x
    apply Prod.ext
    · exact h
    exact Prod.ext rfl (Prod.ext rfl ht)
  · intro h
    rw [← h]
    exact ⟨rfl,rfl⟩

theorem right15_zero (x : Blocks) : x ∈ fifteen.opposite.selected ↔ x = 0 := by
  rw [BoundaryProjectors.Pair.mem_opposite]
  constructor
  · rintro ⟨hu, hi⟩
    have h1 := congrArg Prod.fst hu
    have h2 := congrArg Prod.snd hi
    exact Prod.ext h1 h2
  · rintro rfl; exact ⟨map_zero _,map_zero _⟩

theorem embed15_covariant (g : GaugeGroup) (x : Light15) :
    blocksRho g (embed15 x) = embed15 ((quark.prod electronRight.dual) g x) := by
  simp [blocksRho, embed15]

theorem fifteen_gauge_uv (g : GaugeGroup) : uv15.comp (blocksRho g) = (blocksRho g).comp uv15 := by
  ext x <;> simp [uv15,blocksRho]

theorem fifteen_gauge_ir (g : GaugeGroup) : ir15.comp (blocksRho g) = (blocksRho g).comp ir15 := by
  ext x <;> simp [ir15,blocksRho]

/-- The left fifteen is an actual exterior square via the proved branching equivalence. -/
theorem actual_left15_exact (v : ⋀[ℂ]^2 (Fin 6 → ℂ)) :
    branch v ∈ fifteen.selected ↔
      v = StandardSMExterior.algebraicEquiv.symm (embed15 (extract15 (branch v))) := by
  rw [left15_exact]
  constructor
  · intro h
    apply StandardSMExterior.branch_bijective.1
    change branch v = StandardSMExterior.algebraicEquiv
      (StandardSMExterior.algebraicEquiv.symm (embed15 (extract15 (branch v))))
    rw [StandardSMExterior.algebraicEquiv.apply_symm_apply]
    exact h.symm
  · intro h
    rw [h]
    change embed15 (extract15 (StandardSMExterior.algebraicEquiv
      (StandardSMExterior.algebraicEquiv.symm _))) =
        StandardSMExterior.algebraicEquiv (StandardSMExterior.algebraicEquiv.symm _)
    rw [StandardSMExterior.algebraicEquiv.apply_symm_apply]
    rfl

open SU6BoundaryCube in
def twenty : BoundaryProjectors.Pair (K := ℂ) (V := Cube) where
  uv := 0
  ir := LinearMap.id - embed.comp contract
  uv_idem := by simp
  ir_idem := by
    apply LinearMap.ext
    intro v
    change (v - embed (contract v)) - embed (contract (v - embed (contract v))) =
      v - embed (contract v)
    simp [contract_embed]
  commute := by simp

@[simp] theorem left20_zero (x : SU6BoundaryCube.Cube) : x ∈ twenty.selected ↔ x = 0 := by
  rw [BoundaryProjectors.Pair.mem_selected]
  constructor
  · intro h; exact h.1.symm
  · rintro rfl; exact ⟨map_zero _,map_zero _⟩

theorem right20_exact (x : SU6BoundaryCube.Cube) :
    x ∈ twenty.opposite.selected ↔ SU6BoundaryCube.embed (SU6BoundaryCube.contract x) = x := by
  rw [BoundaryProjectors.Pair.mem_opposite]
  change 0 = (0 : SU6BoundaryCube.Cube) ∧ x - _ = 0 ↔ _
  simp only [true_and, sub_eq_zero]
  exact eq_comm

theorem twenty_gauge_ir (g : GaugeGroup) :
    twenty.ir.comp (exteriorPower.map 3 (FundamentalRepresentation.rho (StandardSMGroup.hom g))) =
      (exteriorPower.map 3 (FundamentalRepresentation.rho (StandardSMGroup.hom g))).comp twenty.ir := by
  apply LinearMap.ext
  intro v
  change (exteriorPower.map 3 (FundamentalRepresentation.rho (StandardSMGroup.hom g))) v -
    SU6BoundaryCube.embed (SU6BoundaryCube.contract
      ((exteriorPower.map 3 (FundamentalRepresentation.rho (StandardSMGroup.hom g))) v)) =
    (exteriorPower.map 3 (FundamentalRepresentation.rho (StandardSMGroup.hom g)))
      (v - SU6BoundaryCube.embed (SU6BoundaryCube.contract v))
  simp [SU6BoundaryCube.contract_covariant, SU6BoundaryCube.embed_covariant]

def singletProjection : Six →ₗ[ℂ] Six where
  toFun x := (0, (0,x.2.2))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def six : BoundaryProjectors.Pair (K := ℂ) (V := Six) where
  uv := singletProjection
  ir := singletProjection
  uv_idem := by ext x <;> rfl
  ir_idem := by ext x <;> rfl
  commute := rfl

theorem left6_exact (x : Six) : x ∈ six.selected ↔ (0,(0,x.2.2)) = x := by
  simp [BoundaryProjectors.Pair.mem_selected,six,singletProjection]

theorem right6_exact (x : Six) : x ∈ six.opposite.selected ↔ x.2.2 = 0 := by
  rw [BoundaryProjectors.Pair.mem_opposite]
  simp [six,singletProjection]

theorem six_gauge (g : GaugeGroup) :
    singletProjection.comp (StandardSMGroup.heavy g) =
      (StandardSMGroup.heavy g).comp singletProjection := by
  ext x <;> simp [singletProjection,StandardSMGroup.heavy]

/-- The extra singlet has (+,-), so neither unmixed chirality survives. -/
def one : BoundaryProjectors.Pair (K := ℂ) (V := ℂ) where
  uv := LinearMap.id
  ir := 0
  uv_idem := by simp
  ir_idem := by simp
  commute := by simp

@[simp] theorem left1_zero (x : ℂ) : x ∈ one.selected ↔ x = 0 := by
  simp [BoundaryProjectors.Pair.mem_selected,one,eq_comm]
@[simp] theorem right1_zero (x : ℂ) : x ∈ one.opposite.selected ↔ x = 0 := by
  rw [BoundaryProjectors.Pair.mem_opposite]
  simp [one]

def embed6Right : (Color × Weak) →ₗ[ℂ] Six where
  toFun x := (x.1,(x.2,0))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def extract6Right : Six →ₗ[ℂ] (Color × Weak) :=
  (LinearMap.fst ℂ Color (Weak × ℂ)).prod
    ((LinearMap.fst ℂ Weak ℂ).comp (LinearMap.snd ℂ Color (Weak × ℂ)))

def right6Equiv : (Color × Weak) ≃ₗ[ℂ] six.opposite.selected :=
  six.opposite.equivalence embed6Right extract6Right (fun _ => rfl) (by
    intro v
    rw [right6_exact]
    change v.2.2 = 0 ↔ (v.1,(v.2.1,0)) = v
    constructor
    · intro h; rw [← h]
    · intro h; exact (congrArg (fun x : Six => x.2.2) h).symm)

theorem right6_gauge (g : GaugeGroup) (v : Color × Weak) :
    StandardSMGroup.heavy g (embed6Right v) =
      embed6Right ((downRight.prod (twist weak 3)) g v) := by
  simp [StandardSMGroup.heavy,embed6Right,downRight]


def left15Equiv : Light15 ≃ₗ[ℂ] fifteen.selected :=
  fifteen.equivalence embed15 extract15 extract_embed15 left15_exact

def right20Equiv : Color ≃ₗ[ℂ] twenty.opposite.selected :=
  twenty.opposite.equivalence SU6BoundaryCube.embed SU6BoundaryCube.contract
    SU6BoundaryCube.contract_embed right20_exact

end
end GUT.SU6BoundarySelection
