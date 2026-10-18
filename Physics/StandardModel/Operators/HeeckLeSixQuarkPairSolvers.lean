import Physics.StandardModel.Operators.HeeckLeSixQuarkQuotient

/-! Five even directions in a six-dimensional block, five odd directions in
a nine-dimensional block, and the five remaining scalar equations. The final
coupling is solved by back substitution, not by a supplied inverse matrix. -/
namespace GUT.HeeckLeSixQuarkPairSolvers
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def evenForward (e : Fin 5 → K) : Fin 6 → K :=
  let a := -8*e 0+4*e 1
  let b := -4*e 0+8*e 1
  ![a,b,a-4*e 4,b-8*e 4,8*e 0-4*e 1-8*e 2+4*e 3,
    4*e 0-8*e 1-4*e 2-4*e 3]

def evenDecode (y : Fin 6 → K) : Fin 5 → K :=
  ![(-2*y 0+y 1)/12,(-y 0+2*y 1)/12,
    (-y 0-y 1-y 4-y 5)/12,(y 0-2*y 1+y 4-2*y 5)/12,(y 0-y 2)/4]
def evenResidual (y : Fin 6 → K) : K := 2*y 0-y 1-2*y 2+y 3

def oddForward (o : Fin 5 → K) : Fin 9 → K :=
  let a := -4*o 0+4*o 1
  let b := 4*o 1
  ![a,b,0,a-4*o 4,b-4*o 4,0,-a-4*o 2,-b-4*o 3,0]
def oddDecode (y : Fin 9 → K) : Fin 5 → K :=
  ![(-y 0+y 1)/4,y 1/4,(-y 0-y 6)/4,(-y 1-y 7)/4,(y 0-y 3)/4]
def oddResidual (y : Fin 9 → K) : Fin 4 → K := ![y 2,y 0-y 1-y 3+y 4,y 5,y 8]

def couplingForward (z : Fin 5 → K) : Fin 5 → K :=
  ![6*(z 3-z 2),4*(-z 0+z 2+z 4),2*z 2+2*z 3-4*z 4,
    4*(z 4-z 0),4*(z 0+z 1)]

def couplingDecode (y : Fin 5 → K) : Fin 5 → K :=
  let c := (y 1-y 3)/4
  let f := y 0/6+c
  let g := (c+f)/2-y 2/4
  let a := g-y 3/4
  let b := y 4/4-a
  ![a,b,c,f,g]

theorem evenDecode_forward (e : Fin 5 → K) : evenDecode (evenForward e) = e := by
  ext i
  fin_cases i <;> simp [evenDecode, evenForward] <;> ring

omit [CharZero K] in
theorem evenResidual_forward (e : Fin 5 → K) : evenResidual (evenForward e) = 0 := by
  simp [evenResidual, evenForward]
  ring

theorem oddDecode_forward (o : Fin 5 → K) : oddDecode (oddForward o) = o := by
  ext i
  fin_cases i <;> simp [oddDecode, oddForward]

omit [CharZero K] in
theorem oddResidual_forward (o : Fin 5 → K) : oddResidual (oddForward o) = 0 := by
  ext i
  fin_cases i <;> simp [oddResidual, oddForward]
  all_goals ring

theorem couplingDecode_forward (z : Fin 5 → K) : couplingDecode (couplingForward z) = z := by
  ext i
  fin_cases i <;> simp [couplingDecode, couplingForward] <;> ring

theorem couplingForward_decode (y : Fin 5 → K) : couplingForward (couplingDecode y) = y := by
  ext i
  fin_cases i <;> simp [couplingDecode, couplingForward] <;> ring

def evenDecodeLinear : (Fin 6 → K) →ₗ[K] (Fin 5 → K) where
  toFun := evenDecode
  map_add' x y := by ext i; fin_cases i <;> simp [evenDecode] <;> ring
  map_smul' z x := by ext i; fin_cases i <;> simp [evenDecode] <;> ring

def oddDecodeLinear : (Fin 9 → K) →ₗ[K] (Fin 5 → K) where
  toFun := oddDecode
  map_add' x y := by ext i; fin_cases i <;> simp [oddDecode] <;> ring
  map_smul' z x := by ext i; fin_cases i <;> simp [oddDecode] <;> ring

def evenResidualLinear : (Fin 6 → K) →ₗ[K] K where
  toFun := evenResidual
  map_add' x y := by simp [evenResidual]; ring
  map_smul' z x := by simp [evenResidual]; ring

def oddResidualLinear : (Fin 9 → K) →ₗ[K] (Fin 4 → K) where
  toFun := oddResidual
  map_add' x y := by ext i; fin_cases i <;> simp [oddResidual]; ring
  map_smul' z x := by ext i; fin_cases i <;> simp [oddResidual]; ring

def couplingDecodeLinear : (Fin 5 → K) →ₗ[K] (Fin 5 → K) where
  toFun := couplingDecode
  map_add' x y := by ext i; fin_cases i <;> simp [couplingDecode] <;> ring
  map_smul' z x := by ext i; fin_cases i <;> simp [couplingDecode] <;> ring

end
end GUT.HeeckLeSixQuarkPairSolvers
