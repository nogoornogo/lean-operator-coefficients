import GUT.SU6.Hypercharge.ActualCompactCentralizerLattice

open Math

/-!
# Independence of the chosen semisimple embedding classification block decomposition

Irreducible blocks of dimensions three, two, and one cannot mix under an
intertwiner. Consequently the physical centralizer coordinates and their
integer circle exponents are independent of the chosen semisimple embedding classification certificate.
-/

namespace GUT.ActualBlockChoiceIndependence

open CompactEmbeddingClassification ActualBlockCentralizer ActualCompactCentralizer

noncomputable section

set_option autoImplicit false

variable (iota : ProductGroup →* SU6)
variable (W W' : WeakDoubletData (euclideanDefiningRestriction iota))

abbrev blockSpace : Fin 3 → Type
  | 0 => ColorBlockSpace W
  | 1 => WeakBlockSpace W
  | 2 => SingletBlockSpace W

instance (j : Fin 3) : AddCommGroup (blockSpace iota W j) :=
  match j with
  | 0 => inferInstanceAs (AddCommGroup (ColorBlockSpace W))
  | 1 => inferInstanceAs (AddCommGroup (WeakBlockSpace W))
  | 2 => inferInstanceAs (AddCommGroup (SingletBlockSpace W))

instance (j : Fin 3) : Module ℂ (blockSpace iota W j) :=
  match j with
  | 0 => inferInstanceAs (Module ℂ (ColorBlockSpace W))
  | 1 => inferInstanceAs (Module ℂ (WeakBlockSpace W))
  | 2 => inferInstanceAs (Module ℂ (SingletBlockSpace W))

instance (j : Fin 3) : FiniteDimensional ℂ (blockSpace iota W j) := by
  fin_cases j <;> unfold blockSpace <;> infer_instance

def blockRho (j : Fin 3) : Representation ℂ ProductGroup (blockSpace iota W j) :=
  match j with
  | 0 => colorBlockRepresentation W
  | 1 => weakBlockRepresentation W
  | 2 => singletBlockRepresentation W

instance (j : Fin 3) : Representation.IsIrreducible (blockRho iota W j) := by
  fin_cases j <;> unfold blockRho <;> infer_instance

theorem blockSpace_finrank (j : Fin 3) :
    Module.finrank ℂ (blockSpace iota W j) = 3 - j.val := by
  fin_cases j <;> simp [blockSpace, ColorBlockSpace, WeakBlockSpace, SingletBlockSpace]

def inclusion (j : Fin 3) :
    Representation.IntertwiningMap (blockRho iota W j) (orderedBlockRepresentation W) :=
  match j with
  | 0 => Representation.IntertwiningMap.inl ℂ _ _
  | 1 => (Representation.IntertwiningMap.inr ℂ _ _).comp
      (Representation.IntertwiningMap.inl ℂ _ _)
  | 2 => (Representation.IntertwiningMap.inr ℂ _ _).comp
      (Representation.IntertwiningMap.inr ℂ _ _)

def projection (j : Fin 3) :
    Representation.IntertwiningMap (orderedBlockRepresentation W) (blockRho iota W j) :=
  match j with
  | 0 => Representation.IntertwiningMap.fst ℂ _ _
  | 1 => (Representation.IntertwiningMap.fst ℂ _ _).comp
      (Representation.IntertwiningMap.snd ℂ _ _)
  | 2 => (Representation.IntertwiningMap.snd ℂ _ _).comp
      (Representation.IntertwiningMap.snd ℂ _ _)

theorem offDiagonal_eq_zero
    (f : Representation.IntertwiningMap
      (orderedBlockRepresentation W) (orderedBlockRepresentation W'))
    (j k : Fin 3) (hjk : j ≠ k) (v : blockSpace iota W j) :
    projection iota W' k (f (inclusion iota W j v)) = 0 := by
  have hd : Module.finrank ℂ (blockSpace iota W j) ≠
      Module.finrank ℂ (blockSpace iota W' k) := by
    rw [blockSpace_finrank, blockSpace_finrank]
    intro he
    apply hjk
    apply Fin.ext
    omega
  have hz := BlockCentralizer.intertwiningMap_eq_zero_of_finrank_ne hd
    ((projection iota W' k).comp (f.comp (inclusion iota W j)))
  exact congrArg (fun t => t v) hz

set_option maxHeartbeats 800000 in
theorem scalar_naturality
    (f : Representation.IntertwiningMap
      (orderedBlockRepresentation W) (orderedBlockRepresentation W'))
    (c w s : ℂ) :
    f.comp (orderedBlockScalarIntertwiner W c w s) =
      (orderedBlockScalarIntertwiner W' c w s).comp f := by
  have h01 (v : ColorBlockSpace W) : (f (v, (0, 0))).2.1 = 0 :=
    offDiagonal_eq_zero iota W W' f 0 1 (by decide) v
  have h02 (v : ColorBlockSpace W) : (f (v, (0, 0))).2.2 = 0 :=
    offDiagonal_eq_zero iota W W' f 0 2 (by decide) v
  have h10 (v : WeakBlockSpace W) : (f (0, (v, 0))).1 = 0 :=
    offDiagonal_eq_zero iota W W' f 1 0 (by decide) v
  have h12 (v : WeakBlockSpace W) : (f (0, (v, 0))).2.2 = 0 :=
    offDiagonal_eq_zero iota W W' f 1 2 (by decide) v
  have h20 (v : SingletBlockSpace W) : (f (0, (0, v))).1 = 0 :=
    offDiagonal_eq_zero iota W W' f 2 0 (by decide) v
  have h21 (v : SingletBlockSpace W) : (f (0, (0, v))).2.1 = 0 :=
    offDiagonal_eq_zero iota W W' f 2 1 (by decide) v
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  rintro ⟨a, b, d⟩
  have hx : (a, (b, d)) = (a, (0, 0)) + (0, (b, 0)) + (0, (0, d)) := by simp
  change f (c • a, (w • b, s • d)) =
    (c • (f (a, (b, d))).1, (w • (f (a, (b, d))).2.1, s • (f (a, (b, d))).2.2))
  have hy : (c • a, (w • b, s • d)) =
      c • (a, (0, 0)) + w • (0, (b, 0)) + s • (0, (0, d)) := by simp
  rw [hy, hx, map_add, map_add, map_smul, map_smul, map_smul, map_add, map_add]
  apply Prod.ext
  · simp [h10, h20]
  · apply Prod.ext
    · simp [h01, h21]
    · simp [h02, h12]

theorem complexBlockCoefficients_independent (U : PhysicalCentralizer iota) :
    complexBlockCoefficients iota W U = complexBlockCoefficients iota W' U := by
  let e := representationEquivOrderedBlocks W
  let e' := representationEquivOrderedBlocks W'
  let f := e.symm.trans e'
  let p := complexBlockCoefficients iota W U
  apply Eq.symm
  apply complexBlockCoefficients_eq_of_spec
  have hn := scalar_naturality iota W W' f.toIntertwiningMap p.1 p.2.1 p.2.2
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have hspec := congrArg (fun t => t (e (e'.symm x)))
    (complexBlockCoefficients_spec iota W U)
  have hn' := congrArg (fun t => t (e (e'.symm x))) hn
  simp only [Representation.IntertwiningMap.comp_apply] at hn'
  change e' (centralizerIntertwiner iota U (e'.symm x)) = _
  calc
    _ = f (e (centralizerIntertwiner iota U (e'.symm x))) := by simp [f, e, e']
    _ = f (orderedBlockScalarIntertwiner W p.1 p.2.1 p.2.2 (e (e'.symm x))) := by
      congr 1
      simpa [transportedCentralizerIntertwiner, BlockCentralizer.transportCommutant, e, e', p]
        using hspec
    _ = _ := by simpa [f, e, e'] using hn'

theorem compactBlockCoefficients_independent (U : PhysicalCentralizer iota) :
    compactBlockCoefficients iota W U = compactBlockCoefficients iota W' U := by
  have h := complexBlockCoefficients_independent iota W W' U
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst h
  · apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun p => p.2.1) h
    · apply Subtype.ext
      exact congrArg (fun p => p.2.2) h

theorem physicalCircleHom_independent (mn : ℤ × ℤ) :
    physicalCircleHom iota W mn = physicalCircleHom iota W' mn := by
  apply ContinuousMonoidHom.ext
  intro z
  apply compactBlockCoefficientHom_injective iota W
  change compactBlockCoefficients iota W _ = compactBlockCoefficients iota W _
  rw [compactBlockCoefficients_independent iota W W' (physicalCircleHom iota W' mn z),
    physicalCircleHom_compactBlockCoefficients, physicalCircleHom_compactBlockCoefficients]

end
end GUT.ActualBlockChoiceIndependence
