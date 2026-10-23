import Math.RepresentationTheory.Color.Diagrams.ColorFocusedSource
import Math.RepresentationTheory.Color.Diagrams.ColorFocusPairTrace

/-! A same-owner evaluation pair vanishes on an entire certified actual
color source. The proof uses its actual trace kernel and polarization of the
other leaves, rather than inferring source vanishing from flag evaluations. -/
namespace Math.ColorInternalPairExclusion
set_option autoImplicit false
noncomputable section
open Representation ColorTensorTree ColorTensorFocus ColorFlagTree ColorCertifiedTree
open SU3DefiningExterior SymmetricVertexCertificate
open scoped TensorProduct

def unitVector : Vector := SU3VolumeContractions.basis 0
def unitCovector : Module.Dual ℂ Vector := SU3VolumeContractions.basis.coord 0
theorem unit_pair : unitCovector unitVector = 1 := by simp [unitVector,unitCovector]

theorem positive (t : Tree) (ht : Certified t) (k : ℕ)
    (h : ColorTensorTree.positive (shape t) = ColorTensorTree.negative (shape t)+3*k)
    (sigma : Equiv.Perm (Fin (ColorTensorTree.negative (shape t)+3*k)))
    (s : Fin (ColorTensorTree.negative (shape t)))
    (hs : negativeOwner (shape t) s =
      ColorTreeDiagrams.positiveOwner (shape t) k h (sigma.symm (Fin.castAdd (3*k) s))) :
    (ColorTreeDiagrams.positiveContraction (shape t) k h sigma).comp (ColorFlagTree.split t).embed = 0 := by
  let i := negativeOwner (shape t) s
  obtain ⟨a,ha⟩ := positive_fiber (shape t) i
    (Fin.cast h.symm (sigma.symm (Fin.castAdd (3*k) s))) hs.symm
  obtain ⟨b,hb⟩ := negative_fiber (shape t) i s rfl
  let p := ColorTensorFocus.positiveAt (shape t) i - 1
  let q := ColorTensorFocus.negativeAt (shape t) i - 1
  have hp : ColorTensorFocus.positiveAt (shape t) i = 1+p := by
    have := a.isLt
    dsimp [p]
    omega
  have hq : ColorTensorFocus.negativeAt (shape t) i = 1+q := by
    have := b.isLt
    dsimp [q]
    omega
  have ha' : Fin.cast h.symm (sigma.symm (Fin.castAdd (3*k) s)) =
      positiveIndex (shape t) i (Fin.cast hp.symm (Fin.cast hp a)) :=
    ha.symm.trans (congrArg (positiveIndex (shape t) i) (Fin.ext rfl))
  have hb' : s = negativeIndex (shape t) i (Fin.cast hq.symm (Fin.cast hq b)) :=
    hb.symm.trans (congrArg (negativeIndex (shape t) i) (Fin.ext rfl))
  have hz : (ColorTreeDiagrams.positiveContraction (shape t) k h sigma).toLinearMap.comp
      (ColorFlagTree.split t).embed.toLinearMap = 0 := by
    apply ColorFocusedSource.zero_of_local t ht i
    intro v f x
    let F := ColorFocusPairTrace.positiveForm (shape t) k h sigma i p q hp hq v f
    let H := F.comp (TensorProduct.map (TensorSlotInsertion.insert p (Fin.cast hp a) unitVector)
      (TensorSlotInsertion.insert q (Fin.cast hq b) unitCovector))
    have hf := ColorFocusPairTrace.positive_factor (shape t) k h sigma i p q hp hq v f
      (Fin.cast hp a) (Fin.cast hq b) s ha' hb' unitVector unitCovector unit_pair
    have hc := vertex_certified t ht i
    have he := annihilate rho (vertexAt t i).split hc.symmetric hc.traceless
      ((ColorCertifiedTree.positiveAt t i).symm.trans hp)
      ((ColorCertifiedTree.negativeAt t i).symm.trans hq) F H hf x
    change ColorTreeDiagrams.positiveContraction (shape t) k h sigma
      (ColorTensorFocus.focus (shape t) i v f
        (cast rho hp.symm hq.symm
          (cast rho ((ColorCertifiedTree.positiveAt t i).symm.trans hp)
            ((ColorCertifiedTree.negativeAt t i).symm.trans hq) ((vertexAt t i).split.embed x)))) = 0 at he
    rw [cast_trans] at he
    exact he
  exact IntertwiningMap.ext hz

theorem negative (t : Tree) (ht : Certified t) (k : ℕ)
    (h : ColorTensorTree.negative (shape t) = ColorTensorTree.positive (shape t)+3*k)
    (sigma : Equiv.Perm (Fin (ColorTensorTree.positive (shape t)+3*k)))
    (s : Fin (ColorTensorTree.positive (shape t)))
    (hs : ColorTreeDiagrams.negativeOwner (shape t) k h (sigma.symm (Fin.castAdd (3*k) s)) =
      positiveOwner (shape t) s) :
    (ColorTreeDiagrams.negativeContraction (shape t) k h sigma).comp (ColorFlagTree.split t).embed = 0 := by
  let i := positiveOwner (shape t) s
  obtain ⟨a,ha⟩ := positive_fiber (shape t) i s rfl
  obtain ⟨b,hb⟩ := negative_fiber (shape t) i
    (Fin.cast h.symm (sigma.symm (Fin.castAdd (3*k) s))) hs
  let p := ColorTensorFocus.positiveAt (shape t) i - 1
  let q := ColorTensorFocus.negativeAt (shape t) i - 1
  have hp : ColorTensorFocus.positiveAt (shape t) i = 1+p := by
    have := a.isLt
    dsimp [p]
    omega
  have hq : ColorTensorFocus.negativeAt (shape t) i = 1+q := by
    have := b.isLt
    dsimp [q]
    omega
  have ha' : s = positiveIndex (shape t) i (Fin.cast hp.symm (Fin.cast hp a)) :=
    ha.symm.trans (congrArg (positiveIndex (shape t) i) (Fin.ext rfl))
  have hb' : Fin.cast h.symm (sigma.symm (Fin.castAdd (3*k) s)) =
      negativeIndex (shape t) i (Fin.cast hq.symm (Fin.cast hq b)) :=
    hb.symm.trans (congrArg (negativeIndex (shape t) i) (Fin.ext rfl))
  have hz : (ColorTreeDiagrams.negativeContraction (shape t) k h sigma).toLinearMap.comp
      (ColorFlagTree.split t).embed.toLinearMap = 0 := by
    apply ColorFocusedSource.zero_of_local t ht i
    intro v f x
    let F := ColorFocusPairTrace.negativeForm (shape t) k h sigma i p q hp hq v f
    let H := F.comp (TensorProduct.map (TensorSlotInsertion.insert p (Fin.cast hp a) unitVector)
      (TensorSlotInsertion.insert q (Fin.cast hq b) unitCovector))
    have hf := ColorFocusPairTrace.negative_factor (shape t) k h sigma i p q hp hq v f
      (Fin.cast hp a) (Fin.cast hq b) s ha' hb' unitVector unitCovector unit_pair
    have hc := vertex_certified t ht i
    have he := annihilate rho (vertexAt t i).split hc.symmetric hc.traceless
      ((ColorCertifiedTree.positiveAt t i).symm.trans hp)
      ((ColorCertifiedTree.negativeAt t i).symm.trans hq) F H hf x
    change ColorTreeDiagrams.negativeContraction (shape t) k h sigma
      (ColorTensorFocus.focus (shape t) i v f
        (cast rho hp.symm hq.symm
          (cast rho ((ColorCertifiedTree.positiveAt t i).symm.trans hp)
            ((ColorCertifiedTree.negativeAt t i).symm.trans hq) ((vertexAt t i).split.embed x)))) = 0 at he
    rw [cast_trans] at he
    exact he
  exact IntertwiningMap.ext hz

end
end Math.ColorInternalPairExclusion
