import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkSupport
import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkPairSolvers

/-! Separate the two raw source families and the invariant product blocks.
Array combinations stay abstract until a component connection is checked. -/
namespace Physics.HeeckLeSixQuarkAssemblyBase
noncomputable section
open LiSixQuarkLocalAction HeeckLeSixQuarkRecipe HeeckLeSixQuarkSupport
variable {K : Type*} [Field K]
attribute [local irreducible] HeeckLeSixQuarkBlocks.orbit

def source0Index : Fin 13 → Fin 25 := ![0,2,3,4,9,10,11,12,13,19,20,21,22]
def source1Index : Fin 12 → Fin 25 := ![1,5,6,7,8,14,15,16,17,18,23,24]

theorem source0_seed (i : Fin 13) : selectedSeed (source0Index i) = 0 := by
  fin_cases i <;> rfl

theorem source1_seed (i : Fin 12) : selectedSeed (source1Index i) = 1 := by
  fin_cases i <;> rfl

def combination {n : ℕ} (columns : Fin n → Arr (K := K)) : (Fin n → K) →ₗ[K] Arr (K := K) where
  toFun v := ∑ j : Fin n, v j • columns j
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' z v := by simp [Finset.smul_sum, smul_smul]

def assemble : (Fin 25 → K) →ₗ[K] Arr (K := K) := combination HeeckLeSixQuarkBlocks.orbit

def source0Assembly : (Fin 13 → K) →ₗ[K] Arr (K := K) :=
  combination (fun i => HeeckLeSixQuarkBlocks.orbit (source0Index i))
def source1Assembly : (Fin 12 → K) →ₗ[K] Arr (K := K) :=
  combination (fun i => HeeckLeSixQuarkBlocks.orbit (source1Index i))

def select0 : (Fin 25 → K) →ₗ[K] (Fin 13 → K) where
  toFun v i := v (source0Index i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def select1 : (Fin 25 → K) →ₗ[K] (Fin 12 → K) where
  toFun v i := v (source1Index i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def weave (a : Fin 13 → K) (b : Fin 12 → K) : Fin 25 → K :=
  ![a 0,b 0,a 1,a 2,a 3,b 1,b 2,b 3,b 4,a 4,a 5,a 6,a 7,a 8,
    b 5,b 6,b 7,b 8,b 9,a 9,a 10,a 11,a 12,b 10,b 11]

def weaveLinear : ((Fin 13 → K) × (Fin 12 → K)) →ₗ[K] (Fin 25 → K) where
  toFun ab := weave ab.1 ab.2
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' z x := by ext i; fin_cases i <;> rfl

theorem weave_select (v : Fin 25 → K) : weave (select0 v) (select1 v) = v := by
  ext i
  fin_cases i <;> rfl

theorem assemble_weave (a : Fin 13 → K) (b : Fin 12 → K) :
    assemble (weave a b) = source0Assembly a+source1Assembly b := by
  ext p q
  simp [assemble, combination, source0Assembly, source1Assembly, weave,
    source0Index, source1Index, Fin.sum_univ_succ, smul_eq_mul]
  ring

theorem assemble_split (v : Fin 25 → K) :
    assemble v = source0Assembly (select0 v)+source1Assembly (select1 v) := by
  have h := assemble_weave (select0 v) (select1 v)
  rw [weave_select] at h
  exact h

def top : Arr (K := K) →ₗ[K] (Fin 10 → K) where
  toFun c := ![c 0 0,c 0 1,c 0 2,c 0 3,c 0 4,c 1 0,c 1 1,c 1 2,c 1 3,c 1 4]
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl

def even : Arr (K := K) →ₗ[K] (Fin 6 → K) where
  toFun c := ![c 2 0,c 2 1,c 3 0,c 3 1,c 4 0,c 4 1]
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl

def odd : Arr (K := K) →ₗ[K] (Fin 9 → K) where
  toFun c := ![c 2 2,c 2 3,c 2 4,c 3 2,c 3 3,c 3 4,c 4 2,c 4 3,c 4 4]
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl

def packResidual : (K × (Fin 4 → K)) →ₗ[K] (Fin 5 → K) where
  toFun z := ![z.1,z.2 0,z.2 1,z.2 2,z.2 3]
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl

def residual : Arr (K := K) →ₗ[K] (Fin 5 → K) :=
  packResidual.comp ((HeeckLeSixQuarkPairSolvers.evenResidualLinear.comp even).prod
    (HeeckLeSixQuarkPairSolvers.oddResidualLinear.comp odd))

theorem top_pair_zero (c : Arr (K := K)) (h : PairZero c) : top c = 0 := by
  ext i
  fin_cases i
  · exact (h 0).1
  · exact (h 1).1
  · exact (h 2).1
  · exact (h 3).1
  · exact (h 4).1
  · exact (h 0).2
  · exact (h 1).2
  · exact (h 2).2
  · exact (h 3).2
  · exact (h 4).2

theorem top_source0 (a : Fin 13 → K) : top (source0Assembly a) = 0 := by
  change top (∑ j : Fin 13, a j • HeeckLeSixQuarkBlocks.orbit (source0Index j)) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [map_smul, top_pair_zero _ (orbit_source0_pair_zero _ (source0_seed j)), smul_zero]

end
end Physics.HeeckLeSixQuarkAssemblyBase
