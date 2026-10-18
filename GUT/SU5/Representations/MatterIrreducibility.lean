import GUT.SU5.Representations.MonomialElements
import GUT.SU5.Representations.UnitaryMatter
import Math.RepresentationTheory.Decomposition.BasisIrreducibility

open Math

/-!
# Irreducibility of the actual SU(5) matter actions

Invariant subspaces are closed under coordinate projections obtained from
diagonal SU(5) signs. Determinant-corrected permutations connect their bases.
-/

set_option autoImplicit false

namespace GUT.SU5.MatterIrreducibility

noncomputable section

open Matter MonomialElements
open UnitaryMatter (fiveBasis barFiveBasis tenBasis)

theorem fundamental_diagonal_basis (i j : Fin 5) :
    fundamental (diagonalSign i) (fiveBasis j) = signAt i j • fiveBasis j := by
  rw [diagonalSign_action]
  ext k
  by_cases h : k = j <;> simp [fiveBasis, Pi.basisFun_apply, h]

theorem fundamental_permutation_basis (p : Equiv.Perm (Fin 5)) (i : Fin 5) :
    fundamental (signedPermutation p) (fiveBasis (p i)) = permutationSign p • fiveBasis i := by
  rw [signedPermutation_action]
  congr 1
  ext j
  simp [fiveBasis, Pi.basisFun_apply, Pi.single_apply]

theorem fundamental_project (i : Fin 5) (v : Five) :
    v + fundamental (diagonalSign i) v = (2 * fiveBasis.repr v i) • fiveBasis i := by
  rw [diagonalSign_action]
  ext j
  by_cases h : j = i <;> simp [fiveBasis, Pi.basisFun_apply, signAt, h, two_mul]

theorem fundamental_irreducible : fundamental.IsIrreducible := by
  apply Math.RepresentationTheory.irreducible_of_basis_coordinates fundamental fiveBasis
  · intro S v hv i
    have h := S.toSubmodule.smul_mem (2 : ℂ)⁻¹
      (S.toSubmodule.add_mem hv (S.apply_mem_toSubmodule (diagonalSign i) hv))
    rw [fundamental_project] at h
    change fiveBasis.repr v i • fiveBasis i ∈ S.toSubmodule
    simpa [smul_smul] using h
  · intro i j
    refine ⟨signedPermutation (Equiv.swap i j), ?_⟩
    have h := fundamental_permutation_basis (Equiv.swap i j) j
    simp only [Equiv.swap_apply_right] at h
    rw [h]
    simpa using permutationSign_ne_zero (Equiv.swap i j)

theorem antifundamental_diagonal_coordinate (i j : Fin 5) (v : BarFive) :
    barFiveBasis.repr (antifundamental (diagonalSign i) v) j =
      signAt i j * barFiveBasis.repr v j := by
  simp only [barFiveBasis, Module.Basis.dualBasis_repr]
  change v (fundamental ((diagonalSign i)⁻¹) (fiveBasis j)) = _
  rw [diagonalSign_inv, fundamental_diagonal_basis, map_smul]
  rfl

theorem antifundamental_project (i : Fin 5) (v : BarFive) :
    v + antifundamental (diagonalSign i) v =
      (2 * barFiveBasis.repr v i) • barFiveBasis i := by
  apply barFiveBasis.repr.injective
  ext j
  simp only [map_add, Finsupp.add_apply, map_smul, Finsupp.smul_apply,
    Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
  rw [antifundamental_diagonal_coordinate]
  by_cases h : i = j <;> simp [signAt, h, Ne.symm, two_mul]

theorem antifundamental_irreducible : antifundamental.IsIrreducible := by
  apply Math.RepresentationTheory.irreducible_of_basis_coordinates antifundamental barFiveBasis
  · intro S v hv i
    have h := S.toSubmodule.smul_mem (2 : ℂ)⁻¹
      (S.toSubmodule.add_mem hv (S.apply_mem_toSubmodule (diagonalSign i) hv))
    rw [antifundamental_project] at h
    change barFiveBasis.repr v i • barFiveBasis i ∈ S.toSubmodule
    simpa [smul_smul] using h
  · intro i j
    refine ⟨(signedPermutation (Equiv.swap i j))⁻¹, ?_⟩
    simp only [barFiveBasis, Module.Basis.dualBasis_repr]
    change (fiveBasis.dualBasis i)
      (fundamental (((signedPermutation (Equiv.swap i j))⁻¹)⁻¹) (fiveBasis j)) ≠ 0
    rw [inv_inv]
    have h := fundamental_permutation_basis (Equiv.swap i j) i
    simp only [Equiv.swap_apply_left] at h
    rw [h, map_smul]
    simpa using permutationSign_ne_zero (Equiv.swap i j)

abbrev PairIndex := Set.powersetCard (Fin 5) 2

def orderedPair (s : PairIndex) : Fin 2 ↪o Fin 5 :=
  Set.powersetCard.ofFinEmbEquiv.symm s

def tenSign (i : Fin 5) (s : PairIndex) : ℂ :=
  signAt i (orderedPair s 0) * signAt i (orderedPair s 1)

theorem ten_diagonal_basis (i : Fin 5) (s : PairIndex) :
    ten (diagonalSign i) (tenBasis s) = tenSign i s • tenBasis s := by
  change exteriorPower.map 2 (fundamental (diagonalSign i))
    (fiveBasis.exteriorPower 2 s) = _
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.map_apply_ιMulti]
  simp only [Function.comp_def, fundamental_diagonal_basis]
  rw [AlternatingMap.map_smul_univ]
  simp only [Fin.prod_univ_two]
  simp only [tenSign, orderedPair, tenBasis, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, Function.comp_def]

theorem orderedPair_lt (s : PairIndex) : orderedPair s 0 < orderedPair s 1 :=
  (orderedPair s).strictMono (by decide)

theorem pair_eq_of_entries (s t : PairIndex)
    (h0 : orderedPair s 0 = orderedPair t 0 ∨ orderedPair s 0 = orderedPair t 1)
    (h1 : orderedPair s 1 = orderedPair t 0 ∨ orderedPair s 1 = orderedPair t 1) : s = t := by
  have hs := orderedPair_lt s
  have ht := orderedPair_lt t
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact (hs.ne (h0.trans h1.symm)).elim
  · apply Set.powersetCard.ofFinEmbEquiv.symm.injective
    apply DFunLike.ext
    intro k
    fin_cases k
    · exact h0
    · exact h1
  · rw [h0, h1] at hs
    exact (lt_asymm hs ht).elim
  · exact (hs.ne (h0.trans h1.symm)).elim

theorem tenSign_eq_if (i : Fin 5) (s : PairIndex) :
    tenSign i s = if i = orderedPair s 0 ∨ i = orderedPair s 1 then -1 else 1 := by
  have hn := (orderedPair_lt s).ne
  by_cases h0 : i = orderedPair s 0
  · subst i
    simp [tenSign, signAt, hn.symm]
  · by_cases h1 : i = orderedPair s 1
    · subst i
      simp [tenSign, signAt, hn]
    · simp [tenSign, signAt, h0, h1, Ne.symm h0, Ne.symm h1]

theorem ten_projection_scalar (s t : PairIndex) :
    (1 - tenSign (orderedPair s 0) t) * (1 - tenSign (orderedPair s 1) t) =
      if s = t then (4 : ℂ) else 0 := by
  rw [tenSign_eq_if, tenSign_eq_if]
  by_cases hst : s = t
  · subst t
    norm_num
  · by_cases h0 : orderedPair s 0 = orderedPair t 0 ∨ orderedPair s 0 = orderedPair t 1
    · have h1 : ¬ (orderedPair s 1 = orderedPair t 0 ∨ orderedPair s 1 = orderedPair t 1) :=
        fun h1 => hst (pair_eq_of_entries s t h0 h1)
      simp [hst, h0, h1]
    · simp [hst, h0]

def tenProject (s : PairIndex) : Ten →ₗ[ℂ] Ten :=
  (LinearMap.id - ten (diagonalSign (orderedPair s 0))).comp
    (LinearMap.id - ten (diagonalSign (orderedPair s 1)))

theorem tenProject_basis (s t : PairIndex) :
    tenProject s (tenBasis t) = (if s = t then (4 : ℂ) else 0) • tenBasis t := by
  simp only [tenProject, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    map_sub, ten_diagonal_basis, map_smul]
  rw [← ten_projection_scalar]
  module

theorem tenProject_eq (s : PairIndex) :
    tenProject s = (4 : ℂ) • (tenBasis.coord s).smulRight (tenBasis s) := by
  apply tenBasis.ext
  intro t
  rw [tenProject_basis]
  by_cases h : s = t <;> simp [h, Module.Basis.coord_apply]

theorem ten_project_mem (S : Subrepresentation ten) (v : Ten) (hv : v ∈ S) (s : PairIndex) :
    tenBasis.repr v s • tenBasis s ∈ S := by
  have h1 := S.toSubmodule.sub_mem hv (S.apply_mem_toSubmodule
    (diagonalSign (orderedPair s 1)) hv)
  have h2 := S.toSubmodule.sub_mem h1 (S.apply_mem_toSubmodule
    (diagonalSign (orderedPair s 0)) h1)
  change tenProject s v ∈ S.toSubmodule at h2
  rw [tenProject_eq] at h2
  have h := S.toSubmodule.smul_mem (4 : ℂ)⁻¹ h2
  change tenBasis.repr v s • tenBasis s ∈ S.toSubmodule
  simpa [Module.Basis.coord_apply, smul_smul] using h

theorem ten_basis_transitive (s t : PairIndex) :
    ∃ g, ten g (tenBasis s) = tenBasis t := by
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair
    (orderedPair t) (orderedPair s) (orderedPair t).injective (orderedPair s).injective
  refine ⟨signedPermutation p, ?_⟩
  have hact (k : Fin 2) : fundamental (signedPermutation p) (fiveBasis (orderedPair s k)) =
      permutationSign p • fiveBasis (orderedPair t k) := by
    rw [← hp k]
    exact fundamental_permutation_basis p _
  have hsign : permutationSign p * permutationSign p = 1 := by
    unfold permutationSign
    split_ifs <;> norm_num
  change exteriorPower.map 2 (fundamental (signedPermutation p))
    (fiveBasis.exteriorPower 2 s) = _
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.map_apply_ιMulti]
  change exteriorPower.ιMulti ℂ 2 (fun k =>
    fundamental (signedPermutation p) (fiveBasis (orderedPair s k))) = _
  simp only [hact]
  rw [AlternatingMap.map_smul_univ, Fin.prod_univ_two, hsign, one_smul]
  simp only [tenBasis, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    orderedPair, Function.comp_def]

theorem ten_irreducible : ten.IsIrreducible := by
  let : Nontrivial Ten := Module.nontrivial_of_finrank_pos (R := ℂ) (by rw [ten_finrank]; norm_num)
  apply Math.RepresentationTheory.irreducible_of_basis_coordinates ten tenBasis ten_project_mem
  intro s t
  obtain ⟨g, hg⟩ := ten_basis_transitive s t
  exact ⟨g, by simp [hg]⟩

theorem unitary_fundamental_irreducible : UnitaryMatter.fundamental.toRepresentation.IsIrreducible :=
  Representation.isIrreducible_of_linearEquiv
    UnitaryMatter.fundamentalEquiv.toLinearEquiv
    (fun g v => UnitaryMatter.fundamentalEquiv.toIntertwiningMap.isIntertwining _ _ g v)
    fundamental_irreducible

theorem unitary_antifundamental_irreducible :
    UnitaryMatter.antifundamental.toRepresentation.IsIrreducible :=
  Representation.isIrreducible_of_linearEquiv
    UnitaryMatter.antifundamentalEquiv.toLinearEquiv
    (fun g v => UnitaryMatter.antifundamentalEquiv.toIntertwiningMap.isIntertwining _ _ g v)
    antifundamental_irreducible

theorem unitary_ten_irreducible : UnitaryMatter.ten.toRepresentation.IsIrreducible :=
  Representation.isIrreducible_of_linearEquiv
    UnitaryMatter.tenEquiv.toLinearEquiv
    (fun g v => UnitaryMatter.tenEquiv.toIntertwiningMap.isIntertwining _ _ g v)
    ten_irreducible

theorem unitary_ten_not_equiv_barFive :
    IsEmpty (Representation.Equiv UnitaryMatter.ten.toRepresentation
      UnitaryMatter.antifundamental.toRepresentation) := by
  refine ⟨fun e => ?_⟩
  have h := e.toLinearEquiv.finrank_eq
  rw [UnitaryMatter.tenHilbert_finrank, UnitaryMatter.barFiveHilbert_finrank] at h
  norm_num at h

end

end GUT.SU5.MatterIrreducibility
