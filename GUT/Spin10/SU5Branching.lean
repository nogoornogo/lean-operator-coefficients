import Math.LieGroups.Spin.HalfSpinEigenbasis
import Math.RepresentationTheory.Unitary.UnitaryEigenbasis
import Math.LinearAlgebra.RankFiveExteriorSum
import GUT.SU5.Representations.UnitaryMatter

open Math

/-! Oriented character branching of the actual compact half-spin 16 along
the actual SU(5) lift. No branching or spectral certificate is an input. -/

set_option autoImplicit false

namespace GUT.CompactSpin.SU5Branching

open Math.CompactSpin
noncomputable section

open GUT.SU5

theorem exists_fundamental_eigenbasis (g : CompactSpin.SU5) :
    ∃ (b : Module.Basis (Fin 5) ℂ Matter.Five) (w : Fin 5 → Circle),
      ∀ i, Matter.fundamental g (b i) = (w i : ℂ) • b i := by
  obtain ⟨b, w, he⟩ := UnitaryEigenbasis.exists_element_basis
    UnitaryMatter.fundamental.toRepresentation UnitaryMatter.fundamental_unitary g 5
    UnitaryMatter.fiveHilbert_finrank
  let e := UnitaryMatter.fundamentalEquiv.symm
  refine ⟨b.map e.toLinearEquiv, w, ?_⟩
  intro i
  have hi := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g (b i)
  rw [he i, map_smul] at hi
  simpa only [Module.Basis.map_apply, Representation.Equiv.toLinearEquiv_apply] using hi.symm

theorem product_eigenvalues (g : CompactSpin.SU5)
    (b : Module.Basis (Fin 5) ℂ Matter.Five) (w : Fin 5 → ℂ)
    (he : ∀ i, Matter.fundamental g (b i) = w i • b i) : ∏ i, w i = 1 := by
  have hm : LinearMap.toMatrix b b (Matter.fundamental g) = Matrix.diagonal w := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [LinearMap.toMatrix_apply, he]
    · simp [LinearMap.toMatrix_apply, he, h]
  have hd := LinearMap.det_toMatrix b (Matter.fundamental g)
  rw [hm, Matrix.det_diagonal] at hd
  change (∏ i, w i) = LinearMap.det (Matrix.toLin' g.val) at hd
  rw [LinearMap.det_toLin'] at hd
  exact hd.trans g.property.2

theorem halfSpin_character (g : CompactSpin.SU5) :
    (HalfSpin.representation 5).character (SU5Inclusion g) =
      1 + Matter.ten.character g + Matter.antifundamental.character g := by
  obtain ⟨b, w, he⟩ := exists_fundamental_eigenbasis g
  let bw := b.map (ExteriorComparison.WCoordinates 5).symm
  have hw (i : Fin 5) : ExteriorComparison.WAction g (bw i) = (w i : ℂ) • bw i := by
    apply (ExteriorComparison.WCoordinates 5).injective
    simpa [bw, ExteriorComparison.WAction, Matter.fundamental,
      SpecialUnitaryRealification.complexAction_apply] using he i
  rw [HalfSpinEigenbasis.character g bw (fun i => (w i : ℂ)) hw,
    RankFiveExteriorSum.determinant_one _ (product_eigenvalues g b _ he)]
  have ht : Matter.ten.character g = ∑ s : Set.powersetCard (Fin 5) 2, ∏ i ∈ s.val, (w i : ℂ) :=
    ExteriorEigenbasisTrace.exterior_trace b (Matter.fundamental g) _ he 2
  have hi (i : Fin 5) : Matter.fundamental g⁻¹ (b i) = (w i : ℂ)⁻¹ • b i := by
    apply (Matter.fundamental.apply_bijective g).injective
    rw [Representation.self_inv_apply, map_smul, he, smul_smul,
      inv_mul_cancel₀ (Circle.coe_ne_zero (w i)), one_smul]
  have hb : Matter.antifundamental.character g = ∑ i, (w i : ℂ)⁻¹ := by
    rw [Matter.antifundamental, Representation.char_dual]
    exact ExteriorEigenbasisTrace.trace_eq_sum b _ _ hi
  rw [ht, hb]

theorem unitary_character (g : CompactSpin.SU5) :
    (HalfSpin.unitaryModel 5).toRepresentation.character (SU5Inclusion g) =
      1 + UnitaryMatter.ten.toRepresentation.character g +
        UnitaryMatter.antifundamental.toRepresentation.character g := by
  rw [HalfSpin.unitaryModel_character, halfSpin_character,
    ← Representation.char_iso UnitaryMatter.tenEquiv,
    ← Representation.char_iso UnitaryMatter.antifundamentalEquiv]

theorem unitary_dual_index (g : CompactSpin.SU5) :
    (HalfSpin.unitaryModel 5).toRepresentation.character (SU5Inclusion g) -
        (HalfSpin.unitaryModel 5).toRepresentation.dual.character (SU5Inclusion g) =
      (UnitaryMatter.ten.toRepresentation.character g -
        UnitaryMatter.ten.toRepresentation.dual.character g) +
      (UnitaryMatter.antifundamental.toRepresentation.character g -
        UnitaryMatter.antifundamental.toRepresentation.dual.character g) := by
  rw [Representation.char_dual, ← map_inv, unitary_character, unitary_character,
    Representation.char_dual, Representation.char_dual]
  ring

end

end GUT.CompactSpin.SU5Branching
