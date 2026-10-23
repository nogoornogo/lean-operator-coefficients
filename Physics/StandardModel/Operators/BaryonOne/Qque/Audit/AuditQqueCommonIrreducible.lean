import Physics.StandardModel.Operators.BaryonOne.Qque.QqueCommonIrreducible
import TauCeti.RepresentationTheory.LinearCharacter.Basic
import Lean.Util.CollectAxioms

open Math

namespace Physics.QqueCommonIrreducibleAudit
noncomputable section
open Representation ContinuousRepresentationScope
open scoped TensorProduct

def q : Representation ℂ Circle ℂ := ofLinearCharacter 1
def u : Representation ℂ Circle ℂ := ofLinearCharacter Circle.toUnits
def e : Representation ℂ Circle ℂ := ofLinearCharacter Circle.toUnits⁻¹

theorem q_continuous : IsJointlyContinuous q := by
  change Continuous (fun p : Circle × ℂ => (1 : ℂ) * p.2)
  fun_prop

def product : MultilinearMap ℂ (fun _ : Fin 2 => ℂ) (ℂ ⊗[ℂ] ℂ) :=
  (TensorProduct.lid ℂ ℂ).symm.toLinearMap.compMultilinearMap
    (TensorSquareMultilinear.toMultilinear (TensorProduct.lid ℂ ℂ).toLinearMap)

theorem product_apply (v : Fin 2 → ℂ) : product v = (1 : ℂ) ⊗ₜ[ℂ] (v 0 * v 1) := rfl

def coefficient : SymmetricSquareDescent.equivariantMaps q (u.tprod e) :=
  ⟨⟨product, by
    intro p v
    rw [product_apply, product_apply]
    congr 1
    simpa only [Fin.prod_univ_two, Function.comp_apply] using Equiv.prod_comp p v⟩, by
    intro z v
    simp only [product_apply, q, u, e, ofLinearCharacter_apply,
      Representation.tprod_apply]
    apply (TensorProduct.lid ℂ ℂ).injective
    simp
    ⟩

theorem exists_hom : ∃ f : IntertwiningMap (q.symmetricPower 2) (u.tprod e), f ≠ 0 := by
  refine ⟨SymmetricSquareDescent.descend q (u.tprod e) coefficient, ?_⟩
  intro hz
  have h := congrArg (fun f : IntertwiningMap (q.symmetricPower 2) (u.tprod e) =>
    (TensorProduct.lid ℂ ℂ) (f (SymmetricPower.tprod ℂ ![1, 1]))) hz
  norm_num [SymmetricSquareDescent.descend, coefficient, product_apply] at h

theorem post_product_overlap : QqueCommonIrreducible.Shares q u e :=
  (QqueCommonIrreducible.hom_iff q u e
    (SymmetricSquareSemisimple.of_compact q q_continuous)).mp exists_hom

theorem exterior_nonzero : ∃ f : QqueCoefficientCompleteness.Sector q u e, f ≠ 0 :=
  (QqueCommonIrreducible.coefficient_iff_of_compact q u e q_continuous).mpr
    post_product_overlap

theorem no_q_up_map (f : IntertwiningMap q u) : f = 0 := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change f x = 0
  have h := IntertwiningMap.isIntertwining q u f (-1 : Circle) x
  norm_num [q, u, ofLinearCharacter_apply] at h
  linear_combination (1 / 2 : ℂ) * h

theorem no_q_up_overlap : ¬ CommonIrreducible.Shares q u := by
  let : MeasurableSpace Circle := borel Circle
  let : BorelSpace Circle := ⟨rfl⟩
  exact (CommonIrreducible.all_zero_iff q u
    (CompactIrreducibleQuotient.semisimple q q_continuous)).mp no_q_up_map

end
end Physics.QqueCommonIrreducibleAudit

run_cmd do
  let declarations := [
    ``Physics.QqueCommonIrreducible.hom_iff,
    ``Physics.QqueCommonIrreducible.coefficient_iff,
    ``Physics.QqueCommonIrreducible.full_nonzero_iff,
    ``Physics.QqueCommonIrreducible.full_forbidden_iff,
    ``Physics.QqueCommonIrreducible.coefficient_iff_of_compact,
    ``Physics.QqueCommonIrreducible.full_square_semisimple,
    ``Physics.QqueCommonIrreducible.full_nonzero_iff_of_compact,
    ``Physics.QqueCommonIrreducible.radical_nonzero_iff,
    ``Physics.QqueCommonIrreducible.radical_forbidden_iff,
    ``Physics.QqueCommonIrreducibleAudit.exists_hom,
    ``Physics.QqueCommonIrreducibleAudit.post_product_overlap,
    ``Physics.QqueCommonIrreducibleAudit.exterior_nonzero,
    ``Physics.QqueCommonIrreducibleAudit.no_q_up_map,
    ``Physics.QqueCommonIrreducibleAudit.no_q_up_overlap]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Common constituent: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Common constituent: {declarations.length} strict axiom checks passed"
