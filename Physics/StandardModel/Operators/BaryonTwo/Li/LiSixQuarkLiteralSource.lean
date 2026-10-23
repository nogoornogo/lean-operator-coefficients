import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkExtension
import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkYoungData

/-! Literal epsilon/Young data for Li 2007.07899v1 (5.63), followed by one
explicit extension. Indices 0--9 are printed; index 10 is not in the paper.
Row then column action and the fermionic transfer sign are fixed here. -/
namespace Physics.LiSixQuarkLiteralSource
set_option autoImplicit false
noncomputable section
open SixQuarkInvariant SMEpsilonTensor LiSixQuarkYoungData
attribute [local irreducible] combine

private theorem permutation_bijective : ∀ g : Fin 48,
    Function.Bijective (permutationData g) := by decide +kernel
def permutation (g : Fin 48) : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective (permutationData g) (permutation_bijective g)

private theorem seedColor_bijective : ∀ k : Fin 11,
    Function.Bijective (seedColorData k) := by decide +kernel
def seedColorPerm (k : Fin 11) : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective (seedColorData k) (seedColor_bijective k)

def spinPerm : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective (![0,3,4,1,5,2]) (by decide +kernel)
def paperToRepo : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective (![1,3,4,5,0,2]) (by decide +kernel)

def seed (k : Fin 11) : Coefficient :=
  combine ((SixColorInvariant.pairing 0).domDomCongr (seedColorPerm k))
    ((SixWeylMultilinear.pairing 0).domDomCongr spinPerm)

/-- A literal finite Young sum, before any completeness inverse is used.
The gcd normalization is a nonzero rescaling, not an idempotent claim. -/
def candidate (k : Fin 11) : Coefficient :=
  (∑ g : Fin 48, ((youngWeights k g / normalization k : ℚ) : ℂ) •
    (seed k).domDomCongr (permutation g)).domDomCongr paperToRepo

theorem candidate_invariant (k : Fin 11) : IsInvariant (candidate k) := by
  have hc (C : SixColorInvariant.Coefficient) (h : SixColorInvariant.IsInvariant C)
      (p : Equiv.Perm (Fin 6)) : SixColorInvariant.IsInvariant (C.domDomCongr p) := by
    intro g v
    simpa only [MultilinearMap.domDomCongr_apply, Function.comp_def] using h g (v ∘ p)
  have hw (W : SixWeylMultilinear.Coefficient) (h : SixWeylMultilinear.IsInvariant W)
      (p : Equiv.Perm (Fin 6)) : SixWeylMultilinear.IsInvariant (W.domDomCongr p) := by
    intro g v
    simpa only [MultilinearMap.domDomCongr_apply, Function.comp_def] using h g (v ∘ p)
  have hi (C : SixColorInvariant.Coefficient) (W : SixWeylMultilinear.Coefficient)
      (hC : SixColorInvariant.IsInvariant C) (hW : SixWeylMultilinear.IsInvariant W) :
      IsInvariant (combine C W) := by
    constructor
    · intro g
      have he : (combine C W).compLinearMap (fun _ => colorAction g) = combine C W := by
        apply pure_ext
        intro v s
        simpa only [MultilinearMap.compLinearMap_apply, colorAction,
          TensorProduct.map_tmul, LinearMap.id_apply, combine_apply] using
          congrArg (fun z => z * W s) (hC g v)
      intro v
      exact congrArg (fun f : Coefficient => f v) he
    · intro g
      have he : (combine C W).compLinearMap (fun _ => spinAction g) = combine C W := by
        apply pure_ext
        intro v s
        simpa only [MultilinearMap.compLinearMap_apply, spinAction,
          TensorProduct.map_tmul, LinearMap.id_apply, combine_apply] using
          congrArg (fun z => C v * z) (hW g s)
      intro v
      exact congrArg (fun f : Coefficient => f v) he
  have hp (f : Coefficient) (h : IsInvariant f) (p : Equiv.Perm (Fin 6)) :
      IsInvariant (f.domDomCongr p) := by
    constructor
    · intro g v
      simpa only [MultilinearMap.domDomCongr_apply, Function.comp_def] using h.1 g (v ∘ p)
    · intro g v
      simpa only [MultilinearMap.domDomCongr_apply, Function.comp_def] using h.2 g (v ∘ p)
  have hs : IsInvariant (seed k) := hi _ _
    (hc _ (SixColorInvariant.pairing_invariant 0) _) (hw _ (SixWeylMultilinear.pairing_invariant 0) _)
  apply hp _ _ paperToRepo
  change (∑ g : Fin 48, ((youngWeights k g / normalization k : ℚ) : ℂ) •
    (seed k).domDomCongr (permutation g)) ∈ SixQuarkPermutationCompleteness.invariantSubmodule
  apply Submodule.sum_mem
  intro g hg
  exact Submodule.smul_mem _ _ (hp _ hs _)

end
end Physics.LiSixQuarkLiteralSource
