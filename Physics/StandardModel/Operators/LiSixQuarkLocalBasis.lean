import Physics.StandardModel.Operators.LiSixQuarkCertificate
import Physics.StandardModel.Operators.LiSixQuarkConvention

/-! Literal selected Young-orbit contractions form a basis of the independently
defined invariant six-quark local space. The added seed is explicitly separate. -/
namespace GUT.LiSixQuarkLocalBasis
set_option autoImplicit false
noncomputable section
open SixQuarkInvariant SixQuarkSpeciesQuotient LiSixQuarkConvention
open LiSixQuarkCertificate SixQuarkPermutationCompleteness

def wordCoefficient (w : List (Fin 4)) (f : Coefficient) : Coefficient :=
  w.foldl (fun f g => f.domDomCongr (slotSwap g)) f

theorem word_reconstruct (w : List (Fin 4)) (c : Fin 5 → Fin 5 → ℂ) :
    wordCoefficient w (reconstruct c) =
      reconstruct (w.foldl (fun c g => transform c g) c) := by
  induction w generalizing c with
  | nil => rfl
  | cons g w ih =>
    change wordCoefficient w ((reconstruct c).domDomCongr (slotSwap g)) = _
    rw [← reconstruct_transform]
    exact ih _

def orbitCoefficient (j : Fin 25) : Coefficient :=
  wordCoefficient (selectedWord j) (candidate (selectedSeed j))

theorem orbitCoefficient_eq (j : Fin 25) :
    orbitCoefficient j = reconstruct (orbitArray j) := by
  have hc : candidate (selectedSeed j) = reconstruct (seedCoordinates (selectedSeed j)) := by
    rw [← candidate_coordinates]
    exact (reconstruct_coordinates _ (candidate_invariant _)).symm
  rw [orbitCoefficient, hc, word_reconstruct]
  rfl

def orbitInvariant (j : Fin 25) : invariantSubmodule :=
  ⟨orbitCoefficient j, by rw [orbitCoefficient_eq]; exact reconstruct_invariant _⟩

theorem orbit_coordinates (j : Fin 25) :
    coordinatesEquiv (orbitInvariant j) = orbitArray j := by
  change coordinates (orbitCoefficient j) = _
  rw [orbitCoefficient_eq, coordinates_reconstruct]

theorem coordinate_assembly (v : Fin 25 → ℂ) (p q : Fin 5) :
    coordinateEquiv v p q = ∑ j, v j * orbitArray j p q := by
  have he : coordinateEquiv v = fun p q => ∑ j, v j * orbitArray j p q := by
    apply flatten.injective
    ext i
    rw [coordinateEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    change (basisMatrix.mulVec v) i =
      ∑ j, v j * flatten (orbitArray j) i
    simp only [Matrix.mulVec, dotProduct, orbitArray_agrees]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  exact congrFun (congrFun he p) q

def localEquiv : (Fin 25 → ℂ) ≃ₗ[ℂ] invariantSubmodule :=
  coordinateEquiv.trans coordinatesEquiv.symm

/-- The inverse really assembles the selected literal contractions. -/
theorem localEquiv_assembly (v : Fin 25 → ℂ) :
    localEquiv v = ∑ j, v j • orbitInvariant j := by
  apply coordinatesEquiv.injective
  rw [localEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [map_sum]
  simp only [map_smul, orbit_coordinates]
  ext p q
  simpa [smul_eq_mul] using coordinate_assembly v p q

def basis : Module.Basis (Fin 25) ℂ invariantSubmodule :=
  (Pi.basisFun ℂ (Fin 25)).map localEquiv

theorem basis_apply (j : Fin 25) : basis j = orbitInvariant j := by
  simp [basis, localEquiv_assembly, Pi.basisFun_apply, Pi.single_apply]

theorem orbit_independent : LinearIndependent ℂ orbitInvariant := by
  have hb : ⇑basis = orbitInvariant := funext basis_apply
  rw [← hb]
  exact basis.linearIndependent

theorem literal_reconstruction (f : invariantSubmodule) :
    f = ∑ j, localEquiv.symm f j • orbitInvariant j := by
  rw [← localEquiv_assembly, LinearEquiv.apply_symm_apply]

theorem local_finrank : Module.finrank ℂ invariantSubmodule = 25 := by
  rw [← localEquiv.finrank_eq]
  simp

end
end GUT.LiSixQuarkLocalBasis
