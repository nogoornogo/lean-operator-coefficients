import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkAssemblyBase

/-! Five original up-exchange pairs, three unpaired source-0 words and the
two quotient-kernel combinations. Splitting coefficients into sums/differences
is an invertible change of presentation, not a new operator ansatz. -/
namespace Physics.HeeckLeSixQuarkPairCoordinates
noncomputable section
open LiSixQuarkLocalAction HeeckLeSixQuarkAssemblyBase
variable {K : Type*} [Field K] [CharZero K]
attribute [local irreducible] HeeckLeSixQuarkBlocks.orbit source1Assembly

def pairLeft : Fin 5 → Fin 25 := ![0,3,4,12,13]
def pairRight : Fin 5 → Fin 25 := ![2,9,10,19,20]
def leftIndex : Fin 3 → Fin 25 := ![11,21,22]

def evenColumn (i : Fin 5) : Arr (K := K) :=
  HeeckLeSixQuarkBlocks.orbit (pairLeft i)+HeeckLeSixQuarkBlocks.orbit (pairRight i)
def oddColumn (i : Fin 5) : Arr (K := K) :=
  HeeckLeSixQuarkBlocks.orbit (pairLeft i)-HeeckLeSixQuarkBlocks.orbit (pairRight i)

def evenAssembly : (Fin 5 → K) →ₗ[K] Arr (K := K) := combination evenColumn
def oddAssembly : (Fin 5 → K) →ₗ[K] Arr (K := K) := combination oddColumn
def leftAssembly : (Fin 3 → K) →ₗ[K] Arr (K := K) :=
  combination (fun i => HeeckLeSixQuarkBlocks.orbit (leftIndex i))

def evenSelect (a : Fin 13 → K) : Fin 5 → K :=
  ![(a 0+a 1)/2,(a 2+a 4)/2,(a 3+a 5)/2,(a 7+a 9)/2,(a 8+a 10)/2]
def oddSelect (a : Fin 13 → K) : Fin 5 → K :=
  ![(a 0-a 1)/2,(a 2-a 4)/2,(a 3-a 5)/2,(a 7-a 9)/2,(a 8-a 10)/2]
def leftSelect (a : Fin 13 → K) : Fin 3 → K := ![a 6,a 11,a 12]

def joinZero (e o : Fin 5 → K) (l : Fin 3 → K) : Fin 13 → K :=
  ![e 0+o 0,e 0-o 0,e 1+o 1,e 2+o 2,e 1-o 1,e 2-o 2,l 0,
    e 3+o 3,e 4+o 4,e 3-o 3,e 4-o 4,l 1,l 2]

def joinZeroLinear : ((Fin 5 → K) × (Fin 5 → K) × (Fin 3 → K)) →ₗ[K] (Fin 13 → K) where
  toFun z := joinZero z.1 z.2.1 z.2.2
  map_add' x y := by ext i; fin_cases i <;> simp [joinZero] <;> ring
  map_smul' z x := by ext i; fin_cases i <;> simp [joinZero] <;> ring

theorem join_select (a : Fin 13 → K) : joinZero (evenSelect a) (oddSelect a) (leftSelect a) = a := by
  ext i
  fin_cases i <;> simp [joinZero, evenSelect, oddSelect, leftSelect] <;> ring

theorem source0_split (a : Fin 13 → K) :
    source0Assembly a = evenAssembly (evenSelect a)+oddAssembly (oddSelect a)+leftAssembly (leftSelect a) := by
  ext p q
  simp [source0Assembly, evenAssembly, oddAssembly, leftAssembly, combination,
    evenColumn, oddColumn, source0Index, pairLeft, pairRight, leftIndex,
    evenSelect, oddSelect, leftSelect, Fin.sum_univ_succ, smul_eq_mul]
  ring

def couplingColumn (i : Fin 5) : Arr (K := K) := match i with
  | 0 => HeeckLeSixQuarkBlocks.orbit 11
  | 1 => HeeckLeSixQuarkBlocks.orbit 21
  | 2 => HeeckLeSixQuarkBlocks.orbit 22
  | 3 => source1Assembly HeeckLeSixQuarkQuotient.kernelFirst
  | 4 => source1Assembly HeeckLeSixQuarkQuotient.kernelSecond

def couplingAssembly : (Fin 5 → K) →ₗ[K] Arr (K := K) := combination couplingColumn

def leftOfCoupling : (Fin 5 → K) →ₗ[K] (Fin 3 → K) where
  toFun z := ![z 0,z 1,z 2]
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl

omit [CharZero K] in
theorem coupling_split (z : Fin 5 → K) : couplingAssembly z =
    leftAssembly (leftOfCoupling z)+
      z 3 • source1Assembly HeeckLeSixQuarkQuotient.kernelFirst+
      z 4 • source1Assembly HeeckLeSixQuarkQuotient.kernelSecond := by
  ext p q
  simp [couplingAssembly, couplingColumn, leftAssembly, leftOfCoupling,
    combination, leftIndex, Fin.sum_univ_succ, smul_eq_mul]
  ring

end
end Physics.HeeckLeSixQuarkPairCoordinates
