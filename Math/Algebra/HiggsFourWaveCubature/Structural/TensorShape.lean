import Math.Algebra.HiggsFourWaveCubature.SignControl

/-! Rank-four tensor shape from sign cancellation, swaps and one Hadamard constraint. -/
namespace Math.HiggsFourWaveCubature.Structural
set_option autoImplicit false
set_option Elab.async false
open scoped BigOperators
abbrev Tensor := (Fin 4 → Fin 4) → GaussianInt

def delta (i j : Fin 4) : GaussianInt := if i = j then 1 else 0

private theorem swap_vec (a b i j k l : Fin 4) :
    (fun n => Equiv.swap a b (![i,j,k,l] n)) =
      ![Equiv.swap a b i,Equiv.swap a b j,Equiv.swap a b k,Equiv.swap a b l] := by
  funext n
  fin_cases n <;> rfl

private theorem ite_vec (i j : Fin 4) (a b c d : Fin 2) :
    (fun n => if (![a,b,c,d] n) = 0 then i else j) =
      ![if a=0 then i else j,if b=0 then i else j,
        if c=0 then i else j,if d=0 then i else j] := by
  funext n
  fin_cases n <;> rfl

private theorem pair_moves : ∀ i j : Fin 4, i ≠ j →
    ∃ a b c d : Fin 4,
      Equiv.swap a b (Equiv.swap c d 0) = i ∧
      Equiv.swap a b (Equiv.swap c d 1) = j := by decide +kernel

private theorem pair_relabel (T : Tensor)
    (hs : ∀ a b : Fin 4, ∀ x : Fin 4 → Fin 4,
      T (fun n => Equiv.swap a b (x n)) = T x)
    (i j : Fin 4) (hne : i ≠ j) (v : Fin 4 → Fin 2) :
    T (fun n => if v n = 0 then i else j) =
      T (fun n => if v n = 0 then 0 else 1) := by
  obtain ⟨a,b,c,d,h0,h1⟩ := pair_moves i j hne
  calc
    _ = T (fun n => Equiv.swap a b (Equiv.swap c d
        (if v n = 0 then 0 else 1))) := by
      congr 1
      funext n
      split_ifs <;> simp_all
    _ = T (fun n => Equiv.swap c d (if v n = 0 then 0 else 1)) := hs a b _
    _ = _ := hs c d _

private theorem diagonal_value (T : Tensor)
    (hs : ∀ a b : Fin 4, ∀ x : Fin 4 → Fin 4,
      T (fun n => Equiv.swap a b (x n)) = T x) (i : Fin 4) :
    T ![i,i,i,i] = T ![0,0,0,0] := by
  have h := hs 0 i ![0,0,0,0]
  simpa [swap_vec] using h

private theorem paired_value (T : Tensor)
    (hs : ∀ a b : Fin 4, ∀ x : Fin 4 → Fin 4,
      T (fun n => Equiv.swap a b (x n)) = T x)
    (hzero : ∀ i j k l : Fin 4, ¬Paired i j k l → T ![i,j,k,l] = 0)
    (i j k l : Fin 4) :
    T ![i,j,k,l] =
      if i = j ∧ j = k ∧ k = l then T ![0,0,0,0]
      else if i = j ∧ k = l then T ![0,0,1,1]
      else if i = k ∧ j = l then T ![0,1,0,1]
      else if i = l ∧ j = k then T ![0,1,1,0] else 0 := by
  split_ifs with hd hb hc he
  · rcases hd with ⟨rfl,rfl,rfl⟩
    exact diagonal_value T hs _
  · rcases hb with ⟨rfl,rfl⟩
    have hn : i ≠ k := by
      intro h
      apply hd
      subst_vars
      exact ⟨rfl,rfl,rfl⟩
    simpa [ite_vec] using pair_relabel T hs i k hn ![0,0,1,1]
  · rcases hc with ⟨rfl,rfl⟩
    have hn : i ≠ j := by
      intro h
      apply hd
      subst_vars
      exact ⟨rfl,rfl,rfl⟩
    simpa [ite_vec] using pair_relabel T hs i j hn ![0,1,0,1]
  · rcases he with ⟨rfl,rfl⟩
    have hn : i ≠ j := by
      intro h
      apply hd
      subst_vars
      exact ⟨rfl,rfl,rfl⟩
    simpa [ite_vec] using pair_relabel T hs i j hn ![0,1,1,0]
  · exact hzero i j k l (by simpa only [Paired,not_or] using ⟨hb,hc,he⟩)

private theorem hadamard_diagonal (T : Tensor)
    (hs : ∀ a b : Fin 4, ∀ x : Fin 4 → Fin 4,
      T (fun n => Equiv.swap a b (x n)) = T x)
    (hzero : ∀ i j k l : Fin 4, ¬Paired i j k l → T ![i,j,k,l] = 0)
    (hh : 16*T ![0,0,0,0] =
      ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4, T ![i,j,k,l]) :
    T ![0,0,0,0] = T ![0,0,1,1]+T ![0,1,0,1]+T ![0,1,1,0] := by
  have hsum : (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
      T ![i,j,k,l]) = 4*T ![0,0,0,0] +
      12*(T ![0,0,1,1]+T ![0,1,0,1]+T ![0,1,1,0]) := by
    calc
      _ = ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
          if i=j ∧ j=k ∧ k=l then T ![0,0,0,0]
          else if i=j ∧ k=l then T ![0,0,1,1]
          else if i=k ∧ j=l then T ![0,1,0,1]
          else if i=l ∧ j=k then T ![0,1,1,0] else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        exact paired_value T hs hzero i j k l
      _ = _ := by norm_num [Fin.sum_univ_succ]; ring
  rw [hsum] at hh
  have hz : (12 : GaussianInt)*(T ![0,0,0,0] -
      (T ![0,0,1,1]+T ![0,1,0,1]+T ![0,1,1,0])) = 0 := by
    linear_combination hh
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (by decide))

theorem tensor_shape (T : Tensor)
    (hs : ∀ a b : Fin 4, ∀ x : Fin 4 → Fin 4,
      T (fun n => Equiv.swap a b (x n)) = T x)
    (hzero : ∀ i j k l : Fin 4, ¬Paired i j k l → T ![i,j,k,l] = 0)
    (hh : 16*T ![0,0,0,0] =
      ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4, T ![i,j,k,l])
    (i j k l : Fin 4) :
    T ![i,j,k,l] = T ![0,0,1,1]*delta i j*delta k l+
      T ![0,1,0,1]*delta i k*delta j l+
      T ![0,1,1,0]*delta i l*delta j k := by
  rw [paired_value T hs hzero]
  split_ifs with hd hb hc he
  · rcases hd with ⟨rfl,rfl,rfl⟩
    simpa [delta] using hadamard_diagonal T hs hzero hh
  · rcases hb with ⟨rfl,rfl⟩
    have hn : i ≠ k := by
      intro h
      apply hd
      subst_vars
      exact ⟨rfl,rfl,rfl⟩
    simp [delta,hn]
  · rcases hc with ⟨rfl,rfl⟩
    have hn : i ≠ j := by
      intro h
      apply hd
      subst_vars
      exact ⟨rfl,rfl,rfl⟩
    simp [delta,hn]
  · rcases he with ⟨rfl,rfl⟩
    have hn : i ≠ j := by
      intro h
      apply hd
      subst_vars
      exact ⟨rfl,rfl,rfl⟩
    simp [delta,hn]
  · have hz (a b c d : Fin 4) (h : ¬(a=b ∧ c=d)) :
        delta a b*delta c d = 0 := by
      by_cases hab : a=b <;> by_cases hcd : c=d <;> simp_all [delta]
    simp only [mul_assoc,hz i j k l hb,hz i k j l hc,hz i l j k he,
      mul_zero,add_zero]
end Math.HiggsFourWaveCubature.Structural
