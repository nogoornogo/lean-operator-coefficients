import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkReducedSeeds

/-! The projected sources are determined by nineteen scalar amplitudes in
named Young image directions. Each amplitude is derived from the explicit
five-coordinate epsilon sources, never from a cached projected array. -/
namespace Physics.LiSixQuarkSeedDirections
noncomputable section
open LiSixQuarkLocalAction LiSixQuarkReducedSeeds LiSixQuarkYoungImages
variable {K : Type*} [Field K] [CharZero K]

def direction0 (a b : K) : Arr (K := K) :=
  ![![0,0,(-2)*a,(-2)*a,(-4)*a],
    ![0,0,(2)*a,0,(4)*a],
    ![(1)*b,(1)*b,0,0,0],
    ![(-1)*b,0,0,0,0],
    ![0,(1)*b,0,0,0]]

omit [CharZero K] in
theorem profile0_direction (c : Arr (K := K)) :
    profile0 c = direction0 ((1)*c 0 2+(-3)*c 0 3+(2)*c 1 2+(-3)*c 1 3) ((1)*c 2 0+(1)*c 2 1+(-3)*c 3 0+(3)*c 3 1+(-3)*c 4 0+(3)*c 4 1) := rfl

def direction2 (a b : K) : Arr (K := K) :=
  ![![0,0,(16)*a,0,(8)*a],
    ![0,0,(-8)*a,0,(-16)*a],
    ![(4)*b,(8)*b,0,0,0],
    ![(-4)*b,(4)*b,0,0,0],
    ![0,(-12)*b,0,0,0]]

omit [CharZero K] in
theorem profile2_direction (c : Arr (K := K)) :
    profile2 c = direction2 ((1)*c 0 2+((-1/2))*c 0 3+((-1/2))*c 0 4+((1/2))*c 1 2+((-1/2))*c 1 3+((-1/2))*c 1 4) ((1)*c 2 0+(1)*c 4 0+(-1)*c 4 1) := rfl

def direction4 (a b : K) : Arr (K := K) :=
  ![![(-4)*a,(-8)*a,0,0,0],
    ![(8)*a,(4)*a,0,0,0],
    ![0,0,(8)*b,(4)*b,(8)*b],
    ![0,0,(4)*b,(4)*b,0],
    ![0,0,(-4)*b,0,0]]

omit [CharZero K] in
theorem profile4_direction (c : Arr (K := K)) :
    profile4 c = direction4 ((1)*c 0 0+(-2)*c 0 1+(2)*c 1 0+(-1)*c 1 1) ((1)*c 2 4+(2)*c 3 3+(-1)*c 3 4+(-2)*c 4 2+(2)*c 4 3+(1)*c 4 4) := rfl

def direction6 (a : K) : Arr (K := K) :=
  ![![0,0,0,0,0],
    ![0,0,0,0,0],
    ![0,0,(2)*a,(1)*a,0],
    ![0,0,(3)*a,(1)*a,(2)*a],
    ![0,0,(-3)*a,(-2)*a,(-2)*a]]

omit [CharZero K] in
theorem profile6_direction (c : Arr (K := K)) :
    profile6 c = direction6 ((1)*c 2 2+(-2)*c 2 4+(1)*c 3 2+(-1)*c 4 2) := rfl

def direction7 (a b : K) : Arr (K := K) :=
  ![![(4)*a,(-4)*a,0,0,0],
    ![(-8)*a,(-4)*a,0,0,0],
    ![0,0,(2)*b,(4)*b,(2)*b],
    ![0,0,(4)*b,(4)*b,(6)*b],
    ![0,0,(2)*b,0,0]]

omit [CharZero K] in
theorem profile7_direction (c : Arr (K := K)) :
    profile7 c = direction7 ((1)*c 0 0+(-1)*c 0 1+(-1)*c 1 1) ((1)*c 2 2+(1)*c 2 3+(-1)*c 2 4+(-1)*c 3 2+(1)*c 3 3+(1)*c 3 4+(1)*c 4 2+(1)*c 4 3+(-1)*c 4 4) := rfl

def direction9 (a : K) : Arr (K := K) :=
  ![![0,0,0,0,0],
    ![0,0,0,0,0],
    ![0,0,0,(-8)*a,(-8)*a],
    ![0,0,0,(-8)*a,(-8)*a],
    ![0,0,(16)*a,(16)*a,(16)*a]]

omit [CharZero K] in
theorem profile9_direction (c : Arr (K := K)) :
    profile9 c = direction9 ((1)*c 2 2+((-1/2))*c 2 3+((-1/2))*c 2 4+((1/2))*c 4 2) := rfl

def direction10 (a : K) : Arr (K := K) :=
  ![![(12)*a,0,0,0,0],
    ![0,(12)*a,0,0,0],
    ![0,0,0,0,0],
    ![0,0,0,0,0],
    ![0,0,0,0,0]]

omit [CharZero K] in
theorem profile10_direction (c : Arr (K := K)) :
    profile10 c = direction10 ((1)*c 0 0+(1)*c 1 1) := rfl

def seedDirection (k : Fin 11) : Arr (K := K) := match k with
  | 0 => direction0 (1/4) (1/2)
  | 1 => direction0 (1/2) 0
  | 2 => direction2 (-1/8) (-1/12)
  | 3 => (1/2 : K) • direction2 (-1/4) (1/6)
  | 4 => direction4 (-1/4) (-1/2)
  | 5 => direction4 (-1/4) (1/2)
  | 6 => direction6 1
  | 7 => direction7 (-1/12) 0
  | 8 => direction7 (-1/6) (-1/2)
  | 9 => direction9 (1/8)
  | 10 => direction10 (1/12)

private theorem source0 : reducedSeed (K := K) 0 = seedDirection 0 := by
  simp only [reducedSeed, reducedImage, profile0_direction, seedDirection]
  congr 1 <;> norm_num [reducedRaw, LiSixQuarkReducedAction.colorExtract,
    LiSixQuarkReducedAction.spinExtract, LiSixQuarkSeedRecipe.rawColor,
    LiSixQuarkSeedRecipe.rawSpin, LiSixQuarkRawSource.colorKind]

private theorem source1 : reducedSeed (K := K) 1 = seedDirection 1 := by
  simp only [reducedSeed, reducedImage, profile0_direction, seedDirection]
  congr 1 <;> norm_num [reducedRaw, LiSixQuarkReducedAction.colorExtract,
    LiSixQuarkReducedAction.spinExtract, LiSixQuarkSeedRecipe.rawColor,
    LiSixQuarkSeedRecipe.rawSpin, LiSixQuarkRawSource.colorKind]

private theorem source2 : reducedSeed (K := K) 2 = seedDirection 2 := by
  simp only [reducedSeed, reducedImage, profile2_direction, seedDirection]
  congr 1 <;> norm_num [reducedRaw, LiSixQuarkReducedAction.colorExtract,
    LiSixQuarkReducedAction.spinExtract, LiSixQuarkSeedRecipe.rawColor,
    LiSixQuarkSeedRecipe.rawSpin, LiSixQuarkRawSource.colorKind]

private theorem source3 : reducedSeed (K := K) 3 = seedDirection 3 := by
  simp only [reducedSeed, reducedImage, profile2_direction, seedDirection]
  apply congrArg (fun x => (1/2 : K) • x)
  congr 1 <;> norm_num [reducedRaw, LiSixQuarkReducedAction.colorExtract,
    LiSixQuarkReducedAction.spinExtract, LiSixQuarkSeedRecipe.rawColor,
    LiSixQuarkSeedRecipe.rawSpin, LiSixQuarkRawSource.colorKind]

private theorem source4 : reducedSeed (K := K) 4 = seedDirection 4 := by
  simp only [reducedSeed, reducedImage, profile4_direction, seedDirection]
  congr 1 <;> norm_num [reducedRaw, LiSixQuarkReducedAction.colorExtract,
    LiSixQuarkReducedAction.spinExtract, LiSixQuarkSeedRecipe.rawColor,
    LiSixQuarkSeedRecipe.rawSpin, LiSixQuarkRawSource.colorKind]

private theorem source5 : reducedSeed (K := K) 5 = seedDirection 5 := by
  simp only [reducedSeed, reducedImage, profile4_direction, seedDirection]
  congr 1 <;> norm_num [reducedRaw, LiSixQuarkReducedAction.colorExtract,
    LiSixQuarkReducedAction.spinExtract, LiSixQuarkSeedRecipe.rawColor,
    LiSixQuarkSeedRecipe.rawSpin, LiSixQuarkRawSource.colorKind]

private theorem source6 : reducedSeed (K := K) 6 = seedDirection 6 := by
  simp only [reducedSeed, reducedImage, profile6_direction, seedDirection]
  congr 1
  norm_num [reducedRaw, LiSixQuarkReducedAction.colorExtract,
    LiSixQuarkReducedAction.spinExtract, LiSixQuarkSeedRecipe.rawColor,
    LiSixQuarkSeedRecipe.rawSpin, LiSixQuarkRawSource.colorKind]

private theorem source7 : reducedSeed (K := K) 7 = seedDirection 7 := by
  simp only [reducedSeed, reducedImage, profile7_direction, seedDirection]
  congr 1 <;> norm_num [reducedRaw, LiSixQuarkReducedAction.colorExtract,
    LiSixQuarkReducedAction.spinExtract, LiSixQuarkSeedRecipe.rawColor,
    LiSixQuarkSeedRecipe.rawSpin, LiSixQuarkRawSource.colorKind]

private theorem source8 : reducedSeed (K := K) 8 = seedDirection 8 := by
  simp only [reducedSeed, reducedImage, profile7_direction, seedDirection]
  congr 1 <;> norm_num [reducedRaw, LiSixQuarkReducedAction.colorExtract,
    LiSixQuarkReducedAction.spinExtract, LiSixQuarkSeedRecipe.rawColor,
    LiSixQuarkSeedRecipe.rawSpin, LiSixQuarkRawSource.colorKind]

private theorem source9 : reducedSeed (K := K) 9 = seedDirection 9 := by
  simp only [reducedSeed, reducedImage, profile9_direction, seedDirection]
  congr 1
  norm_num [reducedRaw, LiSixQuarkReducedAction.colorExtract,
    LiSixQuarkReducedAction.spinExtract, LiSixQuarkSeedRecipe.rawColor,
    LiSixQuarkSeedRecipe.rawSpin, LiSixQuarkRawSource.colorKind]

private theorem source10 : reducedSeed (K := K) 10 = seedDirection 10 := by
  simp only [reducedSeed, reducedImage, profile10_direction, seedDirection]
  congr 1
  norm_num [reducedRaw, LiSixQuarkReducedAction.colorExtract,
    LiSixQuarkReducedAction.spinExtract, LiSixQuarkSeedRecipe.rawColor,
    LiSixQuarkSeedRecipe.rawSpin, LiSixQuarkRawSource.colorKind]

theorem reducedSeed_direction (k : Fin 11) : reducedSeed (K := K) k = seedDirection k := by
  fin_cases k
  · exact source0
  · exact source1
  · exact source2
  · exact source3
  · exact source4
  · exact source5
  · exact source6
  · exact source7
  · exact source8
  · exact source9
  · exact source10

end
end Physics.LiSixQuarkSeedDirections
