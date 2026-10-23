import Math.RepresentationTheory.SU2.SL2SymmetricSpan
import Math.RepresentationTheory.Unitary.ContinuousConstructions
import TauCeti.RepresentationTheory.SU2.Exhaustion

/-! Compact continuity follows from the proved symmetric-power spanning
property; no analytic premise on the original SL2 action is added. -/
namespace Math.SL2SpanContinuity
set_option autoImplicit false
noncomputable section
open Representation SL2SymmetricEmbeddings
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
theorem continuous_orbit (rho : Representation ℂ Group V)
    (hr : SL2SymmetricSpan.Spanned rho) (x : V) :
    Continuous (fun u : TauCeti.SU2 => rho (compactInclusion u) x) := by
  have hx : x ∈ Submodule.span ℂ (SL2SymmetricSpan.generators rho) := by rw [hr]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n,q,v,rfl⟩ := hx
    let f := q.toLinearMap.comp (TauCeti.SU2.weightEquiv n).symm.toLinearMap
    have hc : Continuous (fun u =>
        TauCeti.SU2.symPowerModel n u (TauCeti.SU2.weightEquiv n v)) :=
      (continuous_clm_apply.mp (TauCeti.SU2.continuous_symPowerModel n)) _
    have he : (fun u => rho (compactInclusion u) (q v)) =
        fun u => f (TauCeti.SU2.symPowerModel n u (TauCeti.SU2.weightEquiv n v)) := by
      funext u
      rw [← q.isIntertwining _ _ (compactInclusion u), symmetricPower_compact,
        WeakDoubletScalars.symmetricPower_eq]
      change q ((TauCeti.SU2.symPower n) u v) =
        q ((TauCeti.SU2.weightEquiv n).symm
          ((TauCeti.SU2.weightEquiv n) ((TauCeti.SU2.symPower n) u
            ((TauCeti.SU2.weightEquiv n).symm (TauCeti.SU2.weightEquiv n v)))))
      simp
    rw [he]
    exact f.continuous_of_finiteDimensional.comp hc
  | zero => simpa using (continuous_const : Continuous (fun _ : TauCeti.SU2 => (0 : V)))
  | add x y _ _ hx hy =>
    convert hx.add hy using 1
    funext u
    exact map_add _ x y
  | smul c x _ hx =>
    convert hx.const_smul c using 1
    funext u
    exact map_smul _ c x

theorem jointlyContinuous (rho : Representation ℂ Group V)
    (hr : SL2SymmetricSpan.Spanned rho) :
    ContinuousRepresentationScope.IsJointlyContinuous (rho.comp compactInclusion) := by
  let b := Module.finBasis ℂ V
  have he : (fun p : TauCeti.SU2 × V => rho (compactInclusion p.1) p.2) =
      fun p => ∑ i, b.repr p.2 i • rho (compactInclusion p.1) (b i) := by
    funext p
    conv_lhs => rw [← b.sum_repr p.2]
    simp only [map_sum, map_smul]
  unfold ContinuousRepresentationScope.IsJointlyContinuous
  change Continuous (fun p : TauCeti.SU2 × V => rho (compactInclusion p.1) p.2)
  rw [he]
  exact continuous_finsetSum _ (fun i _ =>
    ((b.coord i).continuous_of_finiteDimensional.comp continuous_snd).smul
      ((continuous_orbit rho hr (b i)).comp continuous_fst))

end
end Math.SL2SpanContinuity
