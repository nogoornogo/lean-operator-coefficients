import Math.RepresentationTheory.ExteriorSquareCompression
import GUT.SU6.Representations.ConcreteSU6Representations
import GUT.SU6.Adapters.StandardSMExterior
import GUT.SU5.Matching.HeavyCurrents

open Math

/-! Actual SU(6) exterior currents on the retained first-five-coordinate ten. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU6.ExteriorCurrents
noncomputable section
open ExteriorSquareCoordinates SMEpsilonTensor
open scoped TensorProduct

def includeFive : (Fin 5 → ℂ) →ₗ[ℂ] (Fin 6 → ℂ) where
  toFun x j := if h : j.val < 5 then x ⟨j.val, h⟩ else 0
  map_add' x y := by ext j; by_cases h : j.val < 5 <;> simp [h]
  map_smul' c x := by ext j; by_cases h : j.val < 5 <;> simp [h]

def restrictFive : (Fin 6 → ℂ) →ₗ[ℂ] (Fin 5 → ℂ) where
  toFun x i := x i.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restrict_include (x : Fin 5 → ℂ) : restrictFive (includeFive x) = x := by
  ext i
  simp [restrictFive, includeFive]

def cut (X : Matrix (Fin 6) (Fin 6) ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  X.submatrix Fin.castSucc Fin.castSucc

theorem cut_action (X : Matrix (Fin 6) (Fin 6) ℂ) (x : Fin 5 → ℂ) :
    restrictFive (Matrix.toLin' X (includeFive x)) = Matrix.toLin' (cut X) x := by
  ext i
  simp [restrictFive, includeFive, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_castSucc, cut]

def embedTen : SU5.Matter.Ten →ₗ[ℂ] Space 6 := exteriorPower.map 2 includeFive
def projectTen : Space 6 →ₗ[ℂ] SU5.Matter.Ten := exteriorPower.map 2 restrictFive

theorem project_embed : projectTen.comp embedTen = LinearMap.id := by
  rw [projectTen, embedTen, ← exteriorPower.map_comp]
  have h : restrictFive.comp includeFive = LinearMap.id := LinearMap.ext restrict_include
  rw [h, exteriorPower.map_id]

theorem split_include (x : Fin 5 → ℂ) :
    StandardSMGroup.splitEquiv (includeFive x) =
      ((SU5.FundamentalBranching.splitEquiv x).1,
        ((SU5.FundamentalBranching.splitEquiv x).2, 0)) := rfl

def extendBlocks : SU5.ExteriorSquareBranching.Blocks →ₗ[ℂ] StandardSMExterior.Blocks where
  toFun x := (x.1, (x.2.1, (x.2.2, 0)))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

theorem branch_embed (x : SU5.Matter.Ten) :
    StandardSMExterior.branch (embedTen x) = extendBlocks (SU5.ExteriorSquareBranching.branch x) := by
  have h : StandardSMExterior.branch.comp embedTen =
      extendBlocks.comp SU5.ExteriorSquareBranching.branch := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, embedTen,
      exteriorPower.map_apply_ιMulti, StandardSMExterior.branch_wedge,
      SU5.ExteriorSquareBranching.branch_wedge, Function.comp_apply, split_include]
    simp [StandardSMExterior.pair, SU5.ExteriorSquareBranching.pair, extendBlocks]
  exact DFunLike.congr_fun h x

theorem quark_branch (q : StandardSMGaugeTensor.Quark) :
    StandardSMExterior.branch (embedTen (SU5.HeavyCurrents.quarkEmbed q)) =
      (0, (q, (0, 0))) := by
  rw [branch_embed, SU5.HeavyCurrents.branch_quarkEmbed]
  rfl

theorem quark_covariant (g : StandardSMGaugeTensor.GaugeGroup) (q : StandardSMGaugeTensor.Quark) :
    StandardSMExterior.exteriorRho g (embedTen (SU5.HeavyCurrents.quarkEmbed q)) =
      embedTen (SU5.HeavyCurrents.quarkEmbed (StandardSMGaugeTensor.quark g q)) := by
  apply StandardSMExterior.branch_bijective.1
  have h := Representation.IntertwiningMap.isIntertwining _ _
    StandardSMExterior.branchIntertwiner g (embedTen (SU5.HeavyCurrents.quarkEmbed q))
  change StandardSMExterior.branch _ = StandardSMExterior.blocksRho g
    (StandardSMExterior.branch (embedTen (SU5.HeavyCurrents.quarkEmbed q))) at h
  rw [h, quark_branch, quark_branch]
  simp [StandardSMExterior.blocksRho, Representation.prod]

def coreAction (X : Matrix (Fin 6) (Fin 6) ℂ) : Module.End ℂ SU5.Matter.Ten :=
  projectTen.comp ((infinitesimal X).comp embedTen)

theorem coreAction_eq (X : Matrix (Fin 6) (Fin 6) ℂ) : coreAction X = infinitesimal (cut X) :=
  compress_infinitesimal includeFive restrictFive restrict_include X (cut X) (cut_action X)

abbrev Channel := (Fin 3 × Fin 2) ⊕ Fin 5

def first : Channel → Fin 6
  | .inl (a, _) => (Fin.castAdd 2 a).castSucc
  | .inr i => i.castSucc

def second : Channel → Fin 6
  | .inl (_, w) => (Fin.natAdd 3 w).castSucc
  | .inr _ => 5

def upper (c : Channel) : Matrix (Fin 6) (Fin 6) ℂ := Matrix.single (first c) (second c) 1
def lower (c : Channel) : Matrix (Fin 6) (Fin 6) ℂ := Matrix.single (second c) (first c) 1

theorem cut_upper_core (a : Fin 3) (w : Fin 2) : cut (upper (.inl (a,w))) =
    SU5.HeavyCurrents.upper a w := by
  ext i j
  simp [cut, upper, first, second, SU5.HeavyCurrents.upper, Matrix.single_apply,
    Fin.ext_iff, Nat.add_comm]

theorem cut_lower_core (a : Fin 3) (w : Fin 2) : cut (lower (.inl (a,w))) =
    SU5.HeavyCurrents.lower a w := by
  ext i j
  simp [cut, lower, first, second, SU5.HeavyCurrents.lower, Matrix.single_apply,
    Fin.ext_iff, Nat.add_comm]

theorem cut_upper_extra (i : Fin 5) : cut (upper (.inr i)) = 0 := by
  ext j k
  simp [cut, upper, first, second, Matrix.single_apply, Fin.ext_iff]
  omega

theorem cut_lower_extra (i : Fin 5) : cut (lower (.inr i)) = 0 := by
  ext j k
  simp [cut, lower, first, second, Matrix.single_apply, Fin.ext_iff]
  omega

def upCurrent (c : Channel) : StandardSMGaugeTensor.Quark →ₗ[ℂ] Module.Dual ℂ Color :=
  ((LinearMap.fst ℂ _ _).comp SU5.ExteriorSquareBranching.branch).comp
    ((coreAction (upper c)).comp SU5.HeavyCurrents.quarkEmbed)

def electronCurrent (c : Channel) : StandardSMGaugeTensor.Quark →ₗ[ℂ] Module.Dual ℂ ℂ :=
  ((LinearMap.snd ℂ _ _).comp ((LinearMap.snd ℂ _ _).comp SU5.ExteriorSquareBranching.branch)).comp
    ((coreAction (lower c)).comp SU5.HeavyCurrents.quarkEmbed)

theorem upCurrent_core (a : Fin 3) (w : Fin 2) : upCurrent (.inl (a,w)) =
    SU5.HeavyCurrents.upCurrent a w := by
  simp only [upCurrent, coreAction_eq, cut_upper_core, SU5.HeavyCurrents.upCurrent]

theorem electronCurrent_core (a : Fin 3) (w : Fin 2) : electronCurrent (.inl (a,w)) =
    SU5.HeavyCurrents.electronCurrent a w := by
  simp only [electronCurrent, coreAction_eq, cut_lower_core, SU5.HeavyCurrents.electronCurrent]

theorem upCurrent_extra (i : Fin 5) : upCurrent (.inr i) = 0 := by
  simp [upCurrent, coreAction_eq, cut_upper_extra, infinitesimal_zero]

theorem electronCurrent_extra (i : Fin 5) : electronCurrent (.inr i) = 0 := by
  simp [electronCurrent, coreAction_eq, cut_lower_extra, infinitesimal_zero]

/-- The carrier/action used above is the existing algebraic SU(6) fifteen,
which already has a continuous-unitary realization in the repository. -/
theorem actual_action (g : ActualRestriction.SU6) :
    (CertifiedConstructions.exteriorActual FundamentalRepresentation.actual 2).rho g =
      exteriorPower.map 2 (Matrix.toLin' (g : Matrix (Fin 6) (Fin 6) ℂ)) := rfl

end
end GUT.SU6.ExteriorCurrents
