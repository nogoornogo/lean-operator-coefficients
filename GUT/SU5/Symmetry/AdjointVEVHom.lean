import GUT.SU5.Symmetry.AdjointVEVCover
import Math.LieGroups.SpecialUnitary.AdjointBlockEquiv
import Math.RepresentationTheory.Decomposition.SurjectiveHomTransport

open Math

/-! Exact global-group and algebraic residual-Hom interfaces. The gauge
stabilizer is not identified with an additional flavor group by this result. -/
namespace GUT.SU5.AdjointVEVStabilizer
set_option autoImplicit false
noncomputable section
open StandardModelEmbedding StandardSMGaugeTensor

def unsplit (g : SUN.AdjointStabilizer.Group BlockIndex) : TargetGroup :=
  ⟨Matrix.reindex blockIndexEquiv blockIndexEquiv g.val, by
    constructor
    · change Matrix.reindex blockIndexEquiv blockIndexEquiv g.val ∈
        Matrix.unitaryGroup (Fin 5) ℂ
      rw [Matrix.mem_unitaryGroup_iff]
      have hu := Matrix.mem_unitaryGroup_iff.mp g.property.1
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex]
      change (Matrix.reindexRingEquiv ℂ blockIndexEquiv) g.val *
        (Matrix.reindexRingEquiv ℂ blockIndexEquiv) (star g.val) = 1
      rw [← map_mul, hu, map_one]
    · change Matrix.det (Matrix.reindex blockIndexEquiv blockIndexEquiv g.val) = 1
      rw [Matrix.det_reindex_self]
      exact g.property.2⟩

@[simp] theorem split_unsplit (g : SUN.AdjointStabilizer.Group BlockIndex) :
    split (unsplit g) = g := by
  apply Subtype.ext
  ext i j
  simp [split, unsplit, Matrix.reindex_apply]

@[simp] theorem unsplit_split (g : TargetGroup) : unsplit (split g) = g := by
  apply Subtype.ext
  ext i j
  simp [split, unsplit, Matrix.reindex_apply]

def splitStabilizerEquiv : subgroup ≃*
    SUN.AdjointStabilizer.subgroup
      (SUN.AdjointStabilizer.vacuum (I := Fin 3) (J := Fin 2) 2 (-3)) where
  toFun g := ⟨split g.val, (split_mem_iff g.val).mp g.property⟩
  invFun g := ⟨unsplit g.val, (split_mem_iff _).mpr (by
    rw [split_unsplit]
    exact g.property)⟩
  left_inv g := Subtype.ext (unsplit_split g.val)
  right_inv g := Subtype.ext (split_unsplit g.val)
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Matrix.reindexRingEquiv ℂ blockIndexEquiv.symm).map_mul g.val.val h.val.val

def unitaryBlockEquiv : subgroup ≃* SUN.AdjointStabilizer.blockPairs (Fin 3) (Fin 2) :=
  splitStabilizerEquiv.trans (SUN.AdjointStabilizer.blockEquiv 2 (-3) (by norm_num))

@[simp] theorem unitaryBlockEquiv_color (g : subgroup) :
    (unitaryBlockEquiv g).val.1.val = (split g.val).val.toBlocks₁₁ := rfl

@[simp] theorem unitaryBlockEquiv_weak (g : subgroup) :
    (unitaryBlockEquiv g).val.2.val = (split g.val).val.toBlocks₂₂ := rfl

@[simp] theorem unitaryBlockEquiv_symm (p : SUN.AdjointStabilizer.blockPairs (Fin 3) (Fin 2)) :
    (unitaryBlockEquiv.symm p).val.val = Matrix.reindex blockIndexEquiv blockIndexEquiv
      (Matrix.fromBlocks p.val.1.val 0 0 p.val.2.val) := rfl

variable {V W : Type*} [AddCommMonoid V] [Module ℂ V]
  [AddCommMonoid W] [Module ℂ W]

/-- Pullback to the covering product neither adds nor removes residual Hom maps. -/
def residualHomEquiv (a : Representation ℂ subgroup V) (b : Representation ℂ subgroup W) :
    Representation.IntertwiningMap (a.comp cover) (b.comp cover) ≃ₗ[ℂ]
      Representation.IntertwiningMap a b :=
  SurjectiveHomTransport.homEquiv cover cover_surjective a b

@[simp] theorem residualHomEquiv_apply (a : Representation ℂ subgroup V)
    (b : Representation ℂ subgroup W)
    (f : Representation.IntertwiningMap (a.comp cover) (b.comp cover)) :
    (residualHomEquiv a b f).toLinearMap = f.toLinearMap := rfl

theorem residualHom_nonzero_iff (a : Representation ℂ subgroup V)
    (b : Representation ℂ subgroup W) :
    (∃ f : Representation.IntertwiningMap (a.comp cover) (b.comp cover), f ≠ 0) ↔
      ∃ f : Representation.IntertwiningMap a b, f ≠ 0 :=
  SurjectiveHomTransport.nonzero_iff cover cover_surjective a b

theorem representation_descends_iff (a : Representation ℂ GaugeGroup V) :
    (∃ b : Representation ℂ subgroup V, b.comp cover = a) ↔ hom.ker ≤ a.ker := by
  rw [SurjectiveHomTransport.descends_iff cover cover_surjective, cover_kernel]

/-- Restrictions of actual SU(5) representations automatically satisfy the kernel condition. -/
theorem ambient_representation_descends (a : Representation ℂ TargetGroup V) :
    ∃ b : Representation ℂ subgroup V, b.comp cover = a.comp hom := by
  refine ⟨a.comp subgroup.subtype, ?_⟩
  rfl

end
end GUT.SU5.AdjointVEVStabilizer
