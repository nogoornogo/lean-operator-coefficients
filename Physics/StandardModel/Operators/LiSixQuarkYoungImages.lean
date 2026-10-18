import Physics.StandardModel.Operators.LiSixQuarkReducedAction

/-! Explicit Young image profiles on the four invariant product blocks.
Each nonzero block is a fixed direction times one scalar functional. The
identities hold for arbitrary arrays, independently of any seed or rank table. -/
namespace GUT.LiSixQuarkYoungImages
noncomputable section
open LiSixQuarkLocalAction LiSixQuarkYoungOperators LiSixQuarkReducedAction
variable {K : Type*} [Field K] [CharZero K]

/-- Canonical block directions and their scalar amplitudes for source shape 0. -/
def profile0 (c : Arr (K := K)) : Arr (K := K) :=
  let a := (1)*c 0 2+(-3)*c 0 3+(2)*c 1 2+(-3)*c 1 3
  let b := (1)*c 2 0+(1)*c 2 1+(-3)*c 3 0+(3)*c 3 1+(-3)*c 4 0+(3)*c 4 1
  ![![0,0,(-2)*a,(-2)*a,(-4)*a],
    ![0,0,(2)*a,0,(4)*a],
    ![(1)*b,(1)*b,0,0,0],
    ![(-1)*b,0,0,0,0],
    ![0,(1)*b,0,0,0]]

/-- Canonical block directions and their scalar amplitudes for source shape 2. -/
def profile2 (c : Arr (K := K)) : Arr (K := K) :=
  let a := (1)*c 0 2+((-1/2))*c 0 3+((-1/2))*c 0 4+((1/2))*c 1 2+((-1/2))*c 1 3+((-1/2))*c 1 4
  let b := (1)*c 2 0+(1)*c 4 0+(-1)*c 4 1
  ![![0,0,(16)*a,0,(8)*a],
    ![0,0,(-8)*a,0,(-16)*a],
    ![(4)*b,(8)*b,0,0,0],
    ![(-4)*b,(4)*b,0,0,0],
    ![0,(-12)*b,0,0,0]]

/-- Canonical block directions and their scalar amplitudes for source shape 4. -/
def profile4 (c : Arr (K := K)) : Arr (K := K) :=
  let a := (1)*c 0 0+(-2)*c 0 1+(2)*c 1 0+(-1)*c 1 1
  let b := (1)*c 2 4+(2)*c 3 3+(-1)*c 3 4+(-2)*c 4 2+(2)*c 4 3+(1)*c 4 4
  ![![(-4)*a,(-8)*a,0,0,0],
    ![(8)*a,(4)*a,0,0,0],
    ![0,0,(8)*b,(4)*b,(8)*b],
    ![0,0,(4)*b,(4)*b,0],
    ![0,0,(-4)*b,0,0]]

/-- Canonical block directions and their scalar amplitudes for source shape 6. -/
def profile6 (c : Arr (K := K)) : Arr (K := K) :=
  let a := (1)*c 2 2+(-2)*c 2 4+(1)*c 3 2+(-1)*c 4 2
  ![![0,0,0,0,0],
    ![0,0,0,0,0],
    ![0,0,(2)*a,(1)*a,0],
    ![0,0,(3)*a,(1)*a,(2)*a],
    ![0,0,(-3)*a,(-2)*a,(-2)*a]]

/-- Canonical block directions and their scalar amplitudes for source shape 7. -/
def profile7 (c : Arr (K := K)) : Arr (K := K) :=
  let a := (1)*c 0 0+(-1)*c 0 1+(-1)*c 1 1
  let b := (1)*c 2 2+(1)*c 2 3+(-1)*c 2 4+(-1)*c 3 2+(1)*c 3 3+(1)*c 3 4+(1)*c 4 2+(1)*c 4 3+(-1)*c 4 4
  ![![(4)*a,(-4)*a,0,0,0],
    ![(-8)*a,(-4)*a,0,0,0],
    ![0,0,(2)*b,(4)*b,(2)*b],
    ![0,0,(4)*b,(4)*b,(6)*b],
    ![0,0,(2)*b,0,0]]

/-- Canonical block directions and their scalar amplitudes for source shape 9. -/
def profile9 (c : Arr (K := K)) : Arr (K := K) :=
  let a := (1)*c 2 2+((-1/2))*c 2 3+((-1/2))*c 2 4+((1/2))*c 4 2
  ![![0,0,0,0,0],
    ![0,0,0,0,0],
    ![0,0,0,(-8)*a,(-8)*a],
    ![0,0,0,(-8)*a,(-8)*a],
    ![0,0,(16)*a,(16)*a,(16)*a]]

/-- Canonical block directions and their scalar amplitudes for source shape 10. -/
def profile10 (c : Arr (K := K)) : Arr (K := K) :=
  let a := (1)*c 0 0+(1)*c 1 1
  ![![(12)*a,0,0,0,0],
    ![0,(12)*a,0,0,0],
    ![0,0,0,0,0],
    ![0,0,0,0,0],
    ![0,0,0,0,0]]

omit [CharZero K] in
/-- Apply the named factors before reducing individual block coordinates. -/
theorem young0_apply (t : Fin 4 → Module.End K (Arr (K := K))) (c : Arr (K := K)) :
    young t 0 c = (1/2 : K) •
      (let x := c+t 0 c
       let y := x+t 1 (t 2 (t 3 (t 2 (t 1 x))))
       let z := y-t 2 y+t 2 (t 1 y)
       z-t 1 z) := rfl

omit [CharZero K] in
/-- Apply the named factors before reducing individual block coordinates. -/
theorem young2_apply (t : Fin 4 → Module.End K (Arr (K := K))) (c : Arr (K := K)) :
    young t 2 c = (1/1 : K) •
      (let x := c+t 0 c
       let y := x+t 3 x+t 3 (t 1 (t 2 (t 1 x)))
       let z := y+t 1 (t 2 (t 1 y))
       z-t 1 z) := rfl

omit [CharZero K] in
/-- Apply the named factors before reducing individual block coordinates. -/
theorem young4_apply (t : Fin 4 → Module.End K (Arr (K := K))) (c : Arr (K := K)) :
    young t 4 c = (1/2 : K) •
      (let x := c-t 0 c
       let y := x-t 3 x+t 3 (t 2 x)-t 3 (t 2 (t 1 x))
       let z := y-t 2 y+t 2 (t 1 y)
       z-t 1 z) := rfl

omit [CharZero K] in
/-- Apply the named factors before reducing individual block coordinates. -/
theorem young6_apply (t : Fin 4 → Module.End K (Arr (K := K))) (c : Arr (K := K)) :
    young t 6 c = (1/2 : K) •
      (let x := c-t 0 c
       let y := x+t 1 (t 2 (t 3 (t 2 (t 1 x))))
       let z := y-t 2 y+t 2 (t 1 y)
       z-t 1 z) := rfl

omit [CharZero K] in
/-- Apply the named factors before reducing individual block coordinates. -/
theorem young7_apply (t : Fin 4 → Module.End K (Arr (K := K))) (c : Arr (K := K)) :
    young t 7 c = (1/2 : K) •
      (let x := c-t 0 c
       let y := x+t 2 (t 3 (t 2 x))
       let z := y+t 1 (t 2 (t 1 y))
       let w := z-t 3 z
       w-t 1 w) := rfl

omit [CharZero K] in
/-- Apply the named factors before reducing individual block coordinates. -/
theorem young9_apply (t : Fin 4 → Module.End K (Arr (K := K))) (c : Arr (K := K)) :
    young t 9 c = (1/1 : K) •
      (let x := c-t 0 c
       let y := x+t 3 x+t 3 (t 1 (t 2 (t 1 x)))
       let z := y+t 1 (t 2 (t 1 y))
       z-t 1 z) := rfl

omit [CharZero K] in
/-- Apply the named factors before reducing individual block coordinates. -/
theorem young10_apply (t : Fin 4 → Module.End K (Arr (K := K))) (c : Arr (K := K)) :
    young t 10 c = (1/2 : K) •
      (let x := c-t 0 c
       let y := x+t 3 x+t 3 (t 2 x)+t 3 (t 2 (t 1 x))
       let z := y+t 2 y+t 2 (t 1 y)
       z+t 1 z) := rfl

private theorem image0_entry00 (c : Arr (K := K)) :
    young reducedAction 0 c 0 0 = profile0 c 0 0 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val_zero]
  all_goals ring

private theorem image0_entry01 (c : Arr (K := K)) :
    young reducedAction 0 c 0 1 = profile0 c 0 1 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals ring

private theorem image0_entry02 (c : Arr (K := K)) :
    young reducedAction 0 c 0 2 = profile0 c 0 2 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image0_entry03 (c : Arr (K := K)) :
    young reducedAction 0 c 0 3 = profile0 c 0 3 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image0_entry04 (c : Arr (K := K)) :
    young reducedAction 0 c 0 4 = profile0 c 0 4 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image0_entry10 (c : Arr (K := K)) :
    young reducedAction 0 c 1 0 = profile0 c 1 0 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals ring

private theorem image0_entry11 (c : Arr (K := K)) :
    young reducedAction 0 c 1 1 = profile0 c 1 1 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals ring

private theorem image0_entry12 (c : Arr (K := K)) :
    young reducedAction 0 c 1 2 = profile0 c 1 2 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image0_entry13 (c : Arr (K := K)) :
    young reducedAction 0 c 1 3 = profile0 c 1 3 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image0_entry14 (c : Arr (K := K)) :
    young reducedAction 0 c 1 4 = profile0 c 1 4 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image0_entry20 (c : Arr (K := K)) :
    young reducedAction 0 c 2 0 = profile0 c 2 0 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image0_entry21 (c : Arr (K := K)) :
    young reducedAction 0 c 2 1 = profile0 c 2 1 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image0_entry22 (c : Arr (K := K)) :
    young reducedAction 0 c 2 2 = profile0 c 2 2 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val]
  all_goals ring

private theorem image0_entry23 (c : Arr (K := K)) :
    young reducedAction 0 c 2 3 = profile0 c 2 3 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val]
  all_goals ring

private theorem image0_entry24 (c : Arr (K := K)) :
    young reducedAction 0 c 2 4 = profile0 c 2 4 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val]
  all_goals ring

private theorem image0_entry30 (c : Arr (K := K)) :
    young reducedAction 0 c 3 0 = profile0 c 3 0 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image0_entry31 (c : Arr (K := K)) :
    young reducedAction 0 c 3 1 = profile0 c 3 1 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image0_entry32 (c : Arr (K := K)) :
    young reducedAction 0 c 3 2 = profile0 c 3 2 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val]
  all_goals ring

private theorem image0_entry33 (c : Arr (K := K)) :
    young reducedAction 0 c 3 3 = profile0 c 3 3 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val]
  all_goals ring

private theorem image0_entry34 (c : Arr (K := K)) :
    young reducedAction 0 c 3 4 = profile0 c 3 4 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val]
  all_goals ring

private theorem image0_entry40 (c : Arr (K := K)) :
    young reducedAction 0 c 4 0 = profile0 c 4 0 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image0_entry41 (c : Arr (K := K)) :
    young reducedAction 0 c 4 1 = profile0 c 4 1 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image0_entry42 (c : Arr (K := K)) :
    young reducedAction 0 c 4 2 = profile0 c 4 2 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val]
  all_goals ring

private theorem image0_entry43 (c : Arr (K := K)) :
    young reducedAction 0 c 4 3 = profile0 c 4 3 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val]
  all_goals ring

private theorem image0_entry44 (c : Arr (K := K)) :
    young reducedAction 0 c 4 4 = profile0 c 4 4 := by
  rw [young0_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile0, Matrix.cons_val]
  all_goals ring

private theorem image2_entry00 (c : Arr (K := K)) :
    young reducedAction 2 c 0 0 = profile2 c 0 0 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val_zero]
  all_goals ring

private theorem image2_entry01 (c : Arr (K := K)) :
    young reducedAction 2 c 0 1 = profile2 c 0 1 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals ring

private theorem image2_entry02 (c : Arr (K := K)) :
    young reducedAction 2 c 0 2 = profile2 c 0 2 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image2_entry03 (c : Arr (K := K)) :
    young reducedAction 2 c 0 3 = profile2 c 0 3 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image2_entry04 (c : Arr (K := K)) :
    young reducedAction 2 c 0 4 = profile2 c 0 4 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image2_entry10 (c : Arr (K := K)) :
    young reducedAction 2 c 1 0 = profile2 c 1 0 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals ring

private theorem image2_entry11 (c : Arr (K := K)) :
    young reducedAction 2 c 1 1 = profile2 c 1 1 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals ring

private theorem image2_entry12 (c : Arr (K := K)) :
    young reducedAction 2 c 1 2 = profile2 c 1 2 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image2_entry13 (c : Arr (K := K)) :
    young reducedAction 2 c 1 3 = profile2 c 1 3 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image2_entry14 (c : Arr (K := K)) :
    young reducedAction 2 c 1 4 = profile2 c 1 4 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image2_entry20 (c : Arr (K := K)) :
    young reducedAction 2 c 2 0 = profile2 c 2 0 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image2_entry21 (c : Arr (K := K)) :
    young reducedAction 2 c 2 1 = profile2 c 2 1 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image2_entry22 (c : Arr (K := K)) :
    young reducedAction 2 c 2 2 = profile2 c 2 2 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val]
  all_goals ring

private theorem image2_entry23 (c : Arr (K := K)) :
    young reducedAction 2 c 2 3 = profile2 c 2 3 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val]
  all_goals ring

private theorem image2_entry24 (c : Arr (K := K)) :
    young reducedAction 2 c 2 4 = profile2 c 2 4 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val]
  all_goals ring

private theorem image2_entry30 (c : Arr (K := K)) :
    young reducedAction 2 c 3 0 = profile2 c 3 0 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image2_entry31 (c : Arr (K := K)) :
    young reducedAction 2 c 3 1 = profile2 c 3 1 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image2_entry32 (c : Arr (K := K)) :
    young reducedAction 2 c 3 2 = profile2 c 3 2 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val]
  all_goals ring

private theorem image2_entry33 (c : Arr (K := K)) :
    young reducedAction 2 c 3 3 = profile2 c 3 3 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val]
  all_goals ring

private theorem image2_entry34 (c : Arr (K := K)) :
    young reducedAction 2 c 3 4 = profile2 c 3 4 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val]
  all_goals ring

private theorem image2_entry40 (c : Arr (K := K)) :
    young reducedAction 2 c 4 0 = profile2 c 4 0 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image2_entry41 (c : Arr (K := K)) :
    young reducedAction 2 c 4 1 = profile2 c 4 1 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image2_entry42 (c : Arr (K := K)) :
    young reducedAction 2 c 4 2 = profile2 c 4 2 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val]
  all_goals ring

private theorem image2_entry43 (c : Arr (K := K)) :
    young reducedAction 2 c 4 3 = profile2 c 4 3 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val]
  all_goals ring

private theorem image2_entry44 (c : Arr (K := K)) :
    young reducedAction 2 c 4 4 = profile2 c 4 4 := by
  rw [young2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile2, Matrix.cons_val]
  all_goals ring

private theorem image4_entry00 (c : Arr (K := K)) :
    young reducedAction 4 c 0 0 = profile4 c 0 0 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val_zero]
  all_goals ring

private theorem image4_entry01 (c : Arr (K := K)) :
    young reducedAction 4 c 0 1 = profile4 c 0 1 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals ring

private theorem image4_entry02 (c : Arr (K := K)) :
    young reducedAction 4 c 0 2 = profile4 c 0 2 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image4_entry03 (c : Arr (K := K)) :
    young reducedAction 4 c 0 3 = profile4 c 0 3 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image4_entry04 (c : Arr (K := K)) :
    young reducedAction 4 c 0 4 = profile4 c 0 4 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image4_entry10 (c : Arr (K := K)) :
    young reducedAction 4 c 1 0 = profile4 c 1 0 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals ring

private theorem image4_entry11 (c : Arr (K := K)) :
    young reducedAction 4 c 1 1 = profile4 c 1 1 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals ring

private theorem image4_entry12 (c : Arr (K := K)) :
    young reducedAction 4 c 1 2 = profile4 c 1 2 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image4_entry13 (c : Arr (K := K)) :
    young reducedAction 4 c 1 3 = profile4 c 1 3 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image4_entry14 (c : Arr (K := K)) :
    young reducedAction 4 c 1 4 = profile4 c 1 4 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image4_entry20 (c : Arr (K := K)) :
    young reducedAction 4 c 2 0 = profile4 c 2 0 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image4_entry21 (c : Arr (K := K)) :
    young reducedAction 4 c 2 1 = profile4 c 2 1 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image4_entry22 (c : Arr (K := K)) :
    young reducedAction 4 c 2 2 = profile4 c 2 2 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val]
  all_goals ring

private theorem image4_entry23 (c : Arr (K := K)) :
    young reducedAction 4 c 2 3 = profile4 c 2 3 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val]
  all_goals ring

private theorem image4_entry24 (c : Arr (K := K)) :
    young reducedAction 4 c 2 4 = profile4 c 2 4 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val]
  all_goals ring

private theorem image4_entry30 (c : Arr (K := K)) :
    young reducedAction 4 c 3 0 = profile4 c 3 0 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image4_entry31 (c : Arr (K := K)) :
    young reducedAction 4 c 3 1 = profile4 c 3 1 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image4_entry32 (c : Arr (K := K)) :
    young reducedAction 4 c 3 2 = profile4 c 3 2 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val]
  all_goals ring

private theorem image4_entry33 (c : Arr (K := K)) :
    young reducedAction 4 c 3 3 = profile4 c 3 3 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val]
  all_goals ring

private theorem image4_entry34 (c : Arr (K := K)) :
    young reducedAction 4 c 3 4 = profile4 c 3 4 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val]
  all_goals ring

private theorem image4_entry40 (c : Arr (K := K)) :
    young reducedAction 4 c 4 0 = profile4 c 4 0 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image4_entry41 (c : Arr (K := K)) :
    young reducedAction 4 c 4 1 = profile4 c 4 1 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image4_entry42 (c : Arr (K := K)) :
    young reducedAction 4 c 4 2 = profile4 c 4 2 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val]
  all_goals ring

private theorem image4_entry43 (c : Arr (K := K)) :
    young reducedAction 4 c 4 3 = profile4 c 4 3 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val]
  all_goals ring

private theorem image4_entry44 (c : Arr (K := K)) :
    young reducedAction 4 c 4 4 = profile4 c 4 4 := by
  rw [young4_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile4, Matrix.cons_val]
  all_goals ring

private theorem image6_entry00 (c : Arr (K := K)) :
    young reducedAction 6 c 0 0 = profile6 c 0 0 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val_zero]
  all_goals ring

private theorem image6_entry01 (c : Arr (K := K)) :
    young reducedAction 6 c 0 1 = profile6 c 0 1 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals ring

private theorem image6_entry02 (c : Arr (K := K)) :
    young reducedAction 6 c 0 2 = profile6 c 0 2 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image6_entry03 (c : Arr (K := K)) :
    young reducedAction 6 c 0 3 = profile6 c 0 3 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image6_entry04 (c : Arr (K := K)) :
    young reducedAction 6 c 0 4 = profile6 c 0 4 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image6_entry10 (c : Arr (K := K)) :
    young reducedAction 6 c 1 0 = profile6 c 1 0 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals ring

private theorem image6_entry11 (c : Arr (K := K)) :
    young reducedAction 6 c 1 1 = profile6 c 1 1 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals ring

private theorem image6_entry12 (c : Arr (K := K)) :
    young reducedAction 6 c 1 2 = profile6 c 1 2 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image6_entry13 (c : Arr (K := K)) :
    young reducedAction 6 c 1 3 = profile6 c 1 3 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image6_entry14 (c : Arr (K := K)) :
    young reducedAction 6 c 1 4 = profile6 c 1 4 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image6_entry20 (c : Arr (K := K)) :
    young reducedAction 6 c 2 0 = profile6 c 2 0 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image6_entry21 (c : Arr (K := K)) :
    young reducedAction 6 c 2 1 = profile6 c 2 1 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image6_entry22 (c : Arr (K := K)) :
    young reducedAction 6 c 2 2 = profile6 c 2 2 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val]
  all_goals ring

private theorem image6_entry23 (c : Arr (K := K)) :
    young reducedAction 6 c 2 3 = profile6 c 2 3 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val]
  all_goals ring

private theorem image6_entry24 (c : Arr (K := K)) :
    young reducedAction 6 c 2 4 = profile6 c 2 4 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val]
  all_goals ring

private theorem image6_entry30 (c : Arr (K := K)) :
    young reducedAction 6 c 3 0 = profile6 c 3 0 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image6_entry31 (c : Arr (K := K)) :
    young reducedAction 6 c 3 1 = profile6 c 3 1 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image6_entry32 (c : Arr (K := K)) :
    young reducedAction 6 c 3 2 = profile6 c 3 2 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val]
  all_goals ring

private theorem image6_entry33 (c : Arr (K := K)) :
    young reducedAction 6 c 3 3 = profile6 c 3 3 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val]
  all_goals ring

private theorem image6_entry34 (c : Arr (K := K)) :
    young reducedAction 6 c 3 4 = profile6 c 3 4 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val]
  all_goals ring

private theorem image6_entry40 (c : Arr (K := K)) :
    young reducedAction 6 c 4 0 = profile6 c 4 0 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image6_entry41 (c : Arr (K := K)) :
    young reducedAction 6 c 4 1 = profile6 c 4 1 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image6_entry42 (c : Arr (K := K)) :
    young reducedAction 6 c 4 2 = profile6 c 4 2 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val]
  all_goals ring

private theorem image6_entry43 (c : Arr (K := K)) :
    young reducedAction 6 c 4 3 = profile6 c 4 3 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val]
  all_goals ring

private theorem image6_entry44 (c : Arr (K := K)) :
    young reducedAction 6 c 4 4 = profile6 c 4 4 := by
  rw [young6_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile6, Matrix.cons_val]
  all_goals ring

private theorem image7_entry00 (c : Arr (K := K)) :
    young reducedAction 7 c 0 0 = profile7 c 0 0 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val_zero]
  all_goals ring

private theorem image7_entry01 (c : Arr (K := K)) :
    young reducedAction 7 c 0 1 = profile7 c 0 1 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals ring

private theorem image7_entry02 (c : Arr (K := K)) :
    young reducedAction 7 c 0 2 = profile7 c 0 2 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image7_entry03 (c : Arr (K := K)) :
    young reducedAction 7 c 0 3 = profile7 c 0 3 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image7_entry04 (c : Arr (K := K)) :
    young reducedAction 7 c 0 4 = profile7 c 0 4 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image7_entry10 (c : Arr (K := K)) :
    young reducedAction 7 c 1 0 = profile7 c 1 0 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals ring

private theorem image7_entry11 (c : Arr (K := K)) :
    young reducedAction 7 c 1 1 = profile7 c 1 1 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals ring

private theorem image7_entry12 (c : Arr (K := K)) :
    young reducedAction 7 c 1 2 = profile7 c 1 2 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image7_entry13 (c : Arr (K := K)) :
    young reducedAction 7 c 1 3 = profile7 c 1 3 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image7_entry14 (c : Arr (K := K)) :
    young reducedAction 7 c 1 4 = profile7 c 1 4 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image7_entry20 (c : Arr (K := K)) :
    young reducedAction 7 c 2 0 = profile7 c 2 0 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image7_entry21 (c : Arr (K := K)) :
    young reducedAction 7 c 2 1 = profile7 c 2 1 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image7_entry22 (c : Arr (K := K)) :
    young reducedAction 7 c 2 2 = profile7 c 2 2 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val]
  all_goals ring

private theorem image7_entry23 (c : Arr (K := K)) :
    young reducedAction 7 c 2 3 = profile7 c 2 3 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val]
  all_goals ring

private theorem image7_entry24 (c : Arr (K := K)) :
    young reducedAction 7 c 2 4 = profile7 c 2 4 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val]
  all_goals ring

private theorem image7_entry30 (c : Arr (K := K)) :
    young reducedAction 7 c 3 0 = profile7 c 3 0 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image7_entry31 (c : Arr (K := K)) :
    young reducedAction 7 c 3 1 = profile7 c 3 1 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image7_entry32 (c : Arr (K := K)) :
    young reducedAction 7 c 3 2 = profile7 c 3 2 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val]
  all_goals ring

private theorem image7_entry33 (c : Arr (K := K)) :
    young reducedAction 7 c 3 3 = profile7 c 3 3 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val]
  all_goals ring

private theorem image7_entry34 (c : Arr (K := K)) :
    young reducedAction 7 c 3 4 = profile7 c 3 4 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val]
  all_goals ring

private theorem image7_entry40 (c : Arr (K := K)) :
    young reducedAction 7 c 4 0 = profile7 c 4 0 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image7_entry41 (c : Arr (K := K)) :
    young reducedAction 7 c 4 1 = profile7 c 4 1 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image7_entry42 (c : Arr (K := K)) :
    young reducedAction 7 c 4 2 = profile7 c 4 2 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val]
  all_goals ring

private theorem image7_entry43 (c : Arr (K := K)) :
    young reducedAction 7 c 4 3 = profile7 c 4 3 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val]
  all_goals ring

private theorem image7_entry44 (c : Arr (K := K)) :
    young reducedAction 7 c 4 4 = profile7 c 4 4 := by
  rw [young7_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile7, Matrix.cons_val]
  all_goals ring

private theorem image9_entry00 (c : Arr (K := K)) :
    young reducedAction 9 c 0 0 = profile9 c 0 0 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val_zero]
  all_goals ring

private theorem image9_entry01 (c : Arr (K := K)) :
    young reducedAction 9 c 0 1 = profile9 c 0 1 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals ring

private theorem image9_entry02 (c : Arr (K := K)) :
    young reducedAction 9 c 0 2 = profile9 c 0 2 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image9_entry03 (c : Arr (K := K)) :
    young reducedAction 9 c 0 3 = profile9 c 0 3 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image9_entry04 (c : Arr (K := K)) :
    young reducedAction 9 c 0 4 = profile9 c 0 4 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image9_entry10 (c : Arr (K := K)) :
    young reducedAction 9 c 1 0 = profile9 c 1 0 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals ring

private theorem image9_entry11 (c : Arr (K := K)) :
    young reducedAction 9 c 1 1 = profile9 c 1 1 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals ring

private theorem image9_entry12 (c : Arr (K := K)) :
    young reducedAction 9 c 1 2 = profile9 c 1 2 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image9_entry13 (c : Arr (K := K)) :
    young reducedAction 9 c 1 3 = profile9 c 1 3 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image9_entry14 (c : Arr (K := K)) :
    young reducedAction 9 c 1 4 = profile9 c 1 4 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image9_entry20 (c : Arr (K := K)) :
    young reducedAction 9 c 2 0 = profile9 c 2 0 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image9_entry21 (c : Arr (K := K)) :
    young reducedAction 9 c 2 1 = profile9 c 2 1 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image9_entry22 (c : Arr (K := K)) :
    young reducedAction 9 c 2 2 = profile9 c 2 2 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val]
  all_goals ring

private theorem image9_entry23 (c : Arr (K := K)) :
    young reducedAction 9 c 2 3 = profile9 c 2 3 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val]
  all_goals ring

private theorem image9_entry24 (c : Arr (K := K)) :
    young reducedAction 9 c 2 4 = profile9 c 2 4 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val]
  all_goals ring

private theorem image9_entry30 (c : Arr (K := K)) :
    young reducedAction 9 c 3 0 = profile9 c 3 0 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image9_entry31 (c : Arr (K := K)) :
    young reducedAction 9 c 3 1 = profile9 c 3 1 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image9_entry32 (c : Arr (K := K)) :
    young reducedAction 9 c 3 2 = profile9 c 3 2 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val]
  all_goals ring

private theorem image9_entry33 (c : Arr (K := K)) :
    young reducedAction 9 c 3 3 = profile9 c 3 3 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val]
  all_goals ring

private theorem image9_entry34 (c : Arr (K := K)) :
    young reducedAction 9 c 3 4 = profile9 c 3 4 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val]
  all_goals ring

private theorem image9_entry40 (c : Arr (K := K)) :
    young reducedAction 9 c 4 0 = profile9 c 4 0 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image9_entry41 (c : Arr (K := K)) :
    young reducedAction 9 c 4 1 = profile9 c 4 1 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image9_entry42 (c : Arr (K := K)) :
    young reducedAction 9 c 4 2 = profile9 c 4 2 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val]
  all_goals ring

private theorem image9_entry43 (c : Arr (K := K)) :
    young reducedAction 9 c 4 3 = profile9 c 4 3 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val]
  all_goals ring

private theorem image9_entry44 (c : Arr (K := K)) :
    young reducedAction 9 c 4 4 = profile9 c 4 4 := by
  rw [young9_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile9, Matrix.cons_val]
  all_goals ring

private theorem image10_entry00 (c : Arr (K := K)) :
    young reducedAction 10 c 0 0 = profile10 c 0 0 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val_zero]
  all_goals ring

private theorem image10_entry01 (c : Arr (K := K)) :
    young reducedAction 10 c 0 1 = profile10 c 0 1 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals ring

private theorem image10_entry02 (c : Arr (K := K)) :
    young reducedAction 10 c 0 2 = profile10 c 0 2 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image10_entry03 (c : Arr (K := K)) :
    young reducedAction 10 c 0 3 = profile10 c 0 3 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image10_entry04 (c : Arr (K := K)) :
    young reducedAction 10 c 0 4 = profile10 c 0 4 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image10_entry10 (c : Arr (K := K)) :
    young reducedAction 10 c 1 0 = profile10 c 1 0 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals ring

private theorem image10_entry11 (c : Arr (K := K)) :
    young reducedAction 10 c 1 1 = profile10 c 1 1 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals ring

private theorem image10_entry12 (c : Arr (K := K)) :
    young reducedAction 10 c 1 2 = profile10 c 1 2 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image10_entry13 (c : Arr (K := K)) :
    young reducedAction 10 c 1 3 = profile10 c 1 3 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image10_entry14 (c : Arr (K := K)) :
    young reducedAction 10 c 1 4 = profile10 c 1 4 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image10_entry20 (c : Arr (K := K)) :
    young reducedAction 10 c 2 0 = profile10 c 2 0 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image10_entry21 (c : Arr (K := K)) :
    young reducedAction 10 c 2 1 = profile10 c 2 1 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image10_entry22 (c : Arr (K := K)) :
    young reducedAction 10 c 2 2 = profile10 c 2 2 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val]
  all_goals ring

private theorem image10_entry23 (c : Arr (K := K)) :
    young reducedAction 10 c 2 3 = profile10 c 2 3 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val]
  all_goals ring

private theorem image10_entry24 (c : Arr (K := K)) :
    young reducedAction 10 c 2 4 = profile10 c 2 4 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val]
  all_goals ring

private theorem image10_entry30 (c : Arr (K := K)) :
    young reducedAction 10 c 3 0 = profile10 c 3 0 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image10_entry31 (c : Arr (K := K)) :
    young reducedAction 10 c 3 1 = profile10 c 3 1 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image10_entry32 (c : Arr (K := K)) :
    young reducedAction 10 c 3 2 = profile10 c 3 2 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val]
  all_goals ring

private theorem image10_entry33 (c : Arr (K := K)) :
    young reducedAction 10 c 3 3 = profile10 c 3 3 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val]
  all_goals ring

private theorem image10_entry34 (c : Arr (K := K)) :
    young reducedAction 10 c 3 4 = profile10 c 3 4 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val]
  all_goals ring

private theorem image10_entry40 (c : Arr (K := K)) :
    young reducedAction 10 c 4 0 = profile10 c 4 0 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val_zero, Matrix.cons_val]
  all_goals ring

private theorem image10_entry41 (c : Arr (K := K)) :
    young reducedAction 10 c 4 1 = profile10 c 4 1 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals ring

private theorem image10_entry42 (c : Arr (K := K)) :
    young reducedAction 10 c 4 2 = profile10 c 4 2 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val]
  all_goals ring

private theorem image10_entry43 (c : Arr (K := K)) :
    young reducedAction 10 c 4 3 = profile10 c 4 3 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val]
  all_goals ring

private theorem image10_entry44 (c : Arr (K := K)) :
    young reducedAction 10 c 4 4 = profile10 c 4 4 := by
  rw [young10_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    reducedAction_apply, colorReduced, spinReduced, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  simp only [profile10, Matrix.cons_val]
  all_goals ring

theorem image0 (c : Arr (K := K)) : young reducedAction 0 c = profile0 c := by
  ext p q
  fin_cases p <;> fin_cases q
  · exact image0_entry00 c
  · exact image0_entry01 c
  · exact image0_entry02 c
  · exact image0_entry03 c
  · exact image0_entry04 c
  · exact image0_entry10 c
  · exact image0_entry11 c
  · exact image0_entry12 c
  · exact image0_entry13 c
  · exact image0_entry14 c
  · exact image0_entry20 c
  · exact image0_entry21 c
  · exact image0_entry22 c
  · exact image0_entry23 c
  · exact image0_entry24 c
  · exact image0_entry30 c
  · exact image0_entry31 c
  · exact image0_entry32 c
  · exact image0_entry33 c
  · exact image0_entry34 c
  · exact image0_entry40 c
  · exact image0_entry41 c
  · exact image0_entry42 c
  · exact image0_entry43 c
  · exact image0_entry44 c

theorem image2 (c : Arr (K := K)) : young reducedAction 2 c = profile2 c := by
  ext p q
  fin_cases p <;> fin_cases q
  · exact image2_entry00 c
  · exact image2_entry01 c
  · exact image2_entry02 c
  · exact image2_entry03 c
  · exact image2_entry04 c
  · exact image2_entry10 c
  · exact image2_entry11 c
  · exact image2_entry12 c
  · exact image2_entry13 c
  · exact image2_entry14 c
  · exact image2_entry20 c
  · exact image2_entry21 c
  · exact image2_entry22 c
  · exact image2_entry23 c
  · exact image2_entry24 c
  · exact image2_entry30 c
  · exact image2_entry31 c
  · exact image2_entry32 c
  · exact image2_entry33 c
  · exact image2_entry34 c
  · exact image2_entry40 c
  · exact image2_entry41 c
  · exact image2_entry42 c
  · exact image2_entry43 c
  · exact image2_entry44 c

theorem image4 (c : Arr (K := K)) : young reducedAction 4 c = profile4 c := by
  ext p q
  fin_cases p <;> fin_cases q
  · exact image4_entry00 c
  · exact image4_entry01 c
  · exact image4_entry02 c
  · exact image4_entry03 c
  · exact image4_entry04 c
  · exact image4_entry10 c
  · exact image4_entry11 c
  · exact image4_entry12 c
  · exact image4_entry13 c
  · exact image4_entry14 c
  · exact image4_entry20 c
  · exact image4_entry21 c
  · exact image4_entry22 c
  · exact image4_entry23 c
  · exact image4_entry24 c
  · exact image4_entry30 c
  · exact image4_entry31 c
  · exact image4_entry32 c
  · exact image4_entry33 c
  · exact image4_entry34 c
  · exact image4_entry40 c
  · exact image4_entry41 c
  · exact image4_entry42 c
  · exact image4_entry43 c
  · exact image4_entry44 c

theorem image6 (c : Arr (K := K)) : young reducedAction 6 c = profile6 c := by
  ext p q
  fin_cases p <;> fin_cases q
  · exact image6_entry00 c
  · exact image6_entry01 c
  · exact image6_entry02 c
  · exact image6_entry03 c
  · exact image6_entry04 c
  · exact image6_entry10 c
  · exact image6_entry11 c
  · exact image6_entry12 c
  · exact image6_entry13 c
  · exact image6_entry14 c
  · exact image6_entry20 c
  · exact image6_entry21 c
  · exact image6_entry22 c
  · exact image6_entry23 c
  · exact image6_entry24 c
  · exact image6_entry30 c
  · exact image6_entry31 c
  · exact image6_entry32 c
  · exact image6_entry33 c
  · exact image6_entry34 c
  · exact image6_entry40 c
  · exact image6_entry41 c
  · exact image6_entry42 c
  · exact image6_entry43 c
  · exact image6_entry44 c

theorem image7 (c : Arr (K := K)) : young reducedAction 7 c = profile7 c := by
  ext p q
  fin_cases p <;> fin_cases q
  · exact image7_entry00 c
  · exact image7_entry01 c
  · exact image7_entry02 c
  · exact image7_entry03 c
  · exact image7_entry04 c
  · exact image7_entry10 c
  · exact image7_entry11 c
  · exact image7_entry12 c
  · exact image7_entry13 c
  · exact image7_entry14 c
  · exact image7_entry20 c
  · exact image7_entry21 c
  · exact image7_entry22 c
  · exact image7_entry23 c
  · exact image7_entry24 c
  · exact image7_entry30 c
  · exact image7_entry31 c
  · exact image7_entry32 c
  · exact image7_entry33 c
  · exact image7_entry34 c
  · exact image7_entry40 c
  · exact image7_entry41 c
  · exact image7_entry42 c
  · exact image7_entry43 c
  · exact image7_entry44 c

theorem image9 (c : Arr (K := K)) : young reducedAction 9 c = profile9 c := by
  ext p q
  fin_cases p <;> fin_cases q
  · exact image9_entry00 c
  · exact image9_entry01 c
  · exact image9_entry02 c
  · exact image9_entry03 c
  · exact image9_entry04 c
  · exact image9_entry10 c
  · exact image9_entry11 c
  · exact image9_entry12 c
  · exact image9_entry13 c
  · exact image9_entry14 c
  · exact image9_entry20 c
  · exact image9_entry21 c
  · exact image9_entry22 c
  · exact image9_entry23 c
  · exact image9_entry24 c
  · exact image9_entry30 c
  · exact image9_entry31 c
  · exact image9_entry32 c
  · exact image9_entry33 c
  · exact image9_entry34 c
  · exact image9_entry40 c
  · exact image9_entry41 c
  · exact image9_entry42 c
  · exact image9_entry43 c
  · exact image9_entry44 c

theorem image10 (c : Arr (K := K)) : young reducedAction 10 c = profile10 c := by
  ext p q
  fin_cases p <;> fin_cases q
  · exact image10_entry00 c
  · exact image10_entry01 c
  · exact image10_entry02 c
  · exact image10_entry03 c
  · exact image10_entry04 c
  · exact image10_entry10 c
  · exact image10_entry11 c
  · exact image10_entry12 c
  · exact image10_entry13 c
  · exact image10_entry14 c
  · exact image10_entry20 c
  · exact image10_entry21 c
  · exact image10_entry22 c
  · exact image10_entry23 c
  · exact image10_entry24 c
  · exact image10_entry30 c
  · exact image10_entry31 c
  · exact image10_entry32 c
  · exact image10_entry33 c
  · exact image10_entry34 c
  · exact image10_entry40 c
  · exact image10_entry41 c
  · exact image10_entry42 c
  · exact image10_entry43 c
  · exact image10_entry44 c

end
end GUT.LiSixQuarkYoungImages
