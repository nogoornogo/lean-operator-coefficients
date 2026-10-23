import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkPairBlock

/-! Explicit small linear systems. Every inverse law below is symbolic in
arbitrary complex inputs, not a numerical rank or inverse certificate. -/
namespace Physics.LiSixQuarkBlockSolvers
noncomputable section

/-- The two triples in the color-three/spin-two block. -/
def forward32 (a d : Fin 3 → ℂ) : Fin 6 → ℂ :=
  ![(a 0+a 1+a 2)/2+(-d 0+2*d 1+d 2)/3,
    (a 0-a 1-a 2)/2+(-2*d 0+d 1-d 2)/3,
    (-a 0-a 1+a 2)/2+(d 0+3*d 1+2*d 2)/3,
    -a 1+(-d 0+d 2)/3, -a 2+(-d 1+d 2)/3,
    (a 0+a 1-a 2)/2+(3*d 0+d 1+2*d 2)/3]

def first32 (y : Fin 6 → ℂ) : Fin 3 → ℂ :=
  ![(y 0+y 1-3*y 2+3*y 3-3*y 4+3*y 5)/4,
    (2*y 0-y 1-3*y 3+2*y 4-y 5)/4,
    (y 0-2*y 1-y 2+2*y 3-3*y 4)/4]
def difference32 (y : Fin 6 → ℂ) : Fin 3 → ℂ :=
  ![(-3*y 0-3*y 4+3*y 5)/4, (3*y 1+3*y 2-3*y 3)/4,
    (3*y 0-3*y 1+3*y 3+3*y 4)/4]

theorem first32_forward (a d : Fin 3 → ℂ) : first32 (forward32 a d) = a := by
  ext i; fin_cases i <;> simp [first32, forward32] <;> ring
theorem difference32_forward (a d : Fin 3 → ℂ) : difference32 (forward32 a d) = d := by
  ext i; fin_cases i <;> simp [difference32, forward32] <;> ring

/-- The two triples in the color-two/spin-three block. -/
def forward23 (a s : Fin 3 → ℂ) : Fin 6 → ℂ :=
  ![-a 0+a 1+a 2-2*s 0+s 1-s 2,
    -a 0+a 1+a 2+s 1+s 2, -2*a 0+2*a 2-s 0+2*s 1-s 2,
    a 0+a 1+a 2+s 0-2*s 1-s 2, -2*s 1-2*s 2,
    2*a 0+2*a 1+2*s 0-s 1-s 2]
def first23 (y : Fin 6 → ℂ) : Fin 3 → ℂ :=
  ![(y 0-3*y 1+2*y 3-3*y 4)/4,
    (y 0+2*y 1-y 2-y 3+y 4+y 5)/4,
    (-y 1+y 2+3*y 3-2*y 4-y 5)/4]
def sum23 (y : Fin 6 → ℂ) : Fin 3 → ℂ :=
  ![(-2*y 0+y 1+y 2-y 3+y 4+y 5)/4,
    (-y 1+y 2-y 3-y 4+y 5)/4, (y 1-y 2+y 3-y 4-y 5)/4]

theorem first23_forward (a s : Fin 3 → ℂ) : first23 (forward23 a s) = a := by
  ext i; fin_cases i <;> simp [first23, forward23] <;> ring
theorem sum23_forward (a s : Fin 3 → ℂ) : sum23 (forward23 a s) = s := by
  ext i; fin_cases i <;> simp [sum23, forward23] <;> ring

/-- The nine-dimensional product: one scalar, a triple, a pair and a triple. -/
def forward33 (q : ℂ) (h : Fin 3 → ℂ) (s : Fin 2 → ℂ) (l : Fin 3 → ℂ) : Fin 9 → ℂ :=
  ![-4*q+2*h 0+2*h 1-2*h 2-s 0+s 1,
    -2*q+h 0+h 1-h 2-2*s 0-s 1-l 0-l 1,
    -4*q+2*h 1-2*h 2-s 0+s 1-l 0+l 1,
    -2*q+3*h 0+h 1-h 2-2*s 0-s 1+2*l 1,
    -2*q+h 0+h 1+h 2-2*s 0-s 1-l 0-l 2,
    2*h 0-2*h 2-3*s 0-l 0+2*l 1-l 2,
    2*q-3*h 0-h 1+h 2-s 0-2*s 1+2*l 0,
    -2*h 0-2*h 1+2*l 0+l 1+l 2,
    -2*h 0-2*h 1-3*s 1+2*l 0-l 1-l 2]
def scalar33 (y : Fin 9 → ℂ) : ℂ :=
  (-y 2-2*y 4+y 5+2*y 6-2*y 7-y 8)/12
def first33 (y : Fin 9 → ℂ) : Fin 3 → ℂ :=
  ![(y 0-2*y 2+y 3-y 6)/8,
    (y 0-y 1+y 2+y 3-y 4-y 5+3*y 6-3*y 7-y 8)/8,
    (-y 1-y 2+3*y 4-y 5+y 7-y 8)/8]
def pair33 (y : Fin 9 → ℂ) : Fin 2 → ℂ :=
  ![(-y 0-y 1+y 2+y 3-y 4-y 5-y 6-y 7+y 8)/6,
    (2*y 0-y 1-y 2-2*y 3+y 4+y 5+y 7-y 8)/6]
def last33 (y : Fin 9 → ℂ) : Fin 3 → ℂ :=
  ![(2*y 0-y 1-y 2+y 6)/4, (-y 0-y 1+y 2+y 3)/4,
    (-y 0+2*y 1+y 3-y 4-y 5+y 7-y 8)/4]

theorem scalar33_forward (q : ℂ) (h : Fin 3 → ℂ) (s : Fin 2 → ℂ) (l : Fin 3 → ℂ) :
    scalar33 (forward33 q h s l) = q := by
  simp [scalar33, forward33]; ring
theorem first33_forward (q : ℂ) (h : Fin 3 → ℂ) (s : Fin 2 → ℂ) (l : Fin 3 → ℂ) :
    first33 (forward33 q h s l) = h := by
  ext i; fin_cases i <;> simp [first33, forward33] <;> ring
theorem pair33_forward (q : ℂ) (h : Fin 3 → ℂ) (s : Fin 2 → ℂ) (l : Fin 3 → ℂ) :
    pair33 (forward33 q h s l) = s := by
  ext i; fin_cases i <;> simp [pair33, forward33] <;> ring
theorem last33_forward (q : ℂ) (h : Fin 3 → ℂ) (s : Fin 2 → ℂ) (l : Fin 3 → ℂ) :
    last33 (forward33 q h s l) = l := by
  ext i; fin_cases i <;> simp [last33, forward33] <;> ring

end
end Physics.LiSixQuarkBlockSolvers
