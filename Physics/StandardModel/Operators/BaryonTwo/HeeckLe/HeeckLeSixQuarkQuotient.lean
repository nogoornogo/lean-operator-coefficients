import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkBlocks

/-! The color-pair quotient has dimension 4+6. Twelve source-1 coefficients
are recovered from these ten coordinates and two named kernel parameters.
All reconstruction identities are uniform in the coefficients. -/
namespace Physics.HeeckLeSixQuarkQuotient
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
abbrev Coeff := Fin 12 → K
abbrev Output := Fin 10 → K

def forward (b : Coeff (K := K)) : Output (K := K) :=
  ![-2*b 2-b 3-2*b 4+b 5+b 6-b 7-b 8+b 9+b 10,
    -b 2-2*b 3-b 4+2*b 5+2*b 6+b 7+b 8+2*b 9-b 10,
    b 2-b 3-b 4-b 5-b 6+2*b 7+b 9+2*b 10,
    -b 3-b 5-b 6+b 7+b 8+b 9+b 10,
    2*b 7+2*b 10,
    -2*b 0+2*b 1+2*b 2+2*b 4-b 6-b 9+b 11,
    -b 0+b 1+b 2+b 4-2*b 6-2*b 9-b 11,
    -b 0-b 1-b 2+b 4+b 6-b 9+2*b 11,
    b 6-b 9+b 11, 2*b 11]

/-- The free coordinates are b₈ and b₁₀; the section sets both to zero. -/
def sectionMap (y : Output (K := K)) : Coeff (K := K) :=
  let a := (y 1-2*y 0)/6
  let b := (y 0-2*y 1)/6
  let c := (y 6-2*y 5)/6
  let d := (y 5-2*y 6)/6
  let e := (y 3-y 2)/2
  let f := (y 8-y 7)/2
  let g := y 9/2
  let h := y 4/2
  ![a+e+c+f+g, -a+e+h-c+f, a-e-h,
    b-y 3/2+h+d-y 8/2, a+e, -b-y 3/2-d-y 8/2+g,
    d+y 8/2-g, h, 0, d-y 8/2, 0, g]

def kernelFirst : Coeff (K := K) := ![-1,0,0,1,-1,0,0,0,1,0,0,0]
def kernelSecond : Coeff (K := K) := ![1,-1,1,-1,1,1,0,-1,0,0,1,0]

def solve (y : Output (K := K)) (u v : K) : Coeff (K := K) :=
  sectionMap y+u • kernelFirst+v • kernelSecond

theorem solve_forward (b : Coeff (K := K)) : solve (forward b) (b 8) (b 10) = b := by
  ext i
  fin_cases i <;> simp [solve, sectionMap, forward, kernelFirst, kernelSecond] <;> ring

theorem forward_solve (y : Output (K := K)) (u v : K) : forward (solve y u v) = y := by
  ext i
  fin_cases i <;> simp [solve, sectionMap, forward, kernelFirst, kernelSecond] <;> ring

omit [CharZero K] in
theorem solve_free (y : Output (K := K)) (u v : K) : solve y u v 8 = u ∧ solve y u v 10 = v := by
  simp [solve, sectionMap, kernelFirst, kernelSecond]

theorem section_linear_add (x y : Output (K := K)) : sectionMap (x+y) = sectionMap x+sectionMap y := by
  ext i
  fin_cases i <;> simp [sectionMap] <;> ring

theorem section_linear_smul (z : K) (x : Output (K := K)) : sectionMap (z • x) = z • sectionMap x := by
  ext i
  fin_cases i <;> simp [sectionMap] <;> ring

def sectionLinear : Output (K := K) →ₗ[K] Coeff (K := K) where
  toFun := sectionMap
  map_add' := section_linear_add
  map_smul' := section_linear_smul

end
end Physics.HeeckLeSixQuarkQuotient
