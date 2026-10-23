import Math.Algebra.HiggsFourWaveCubature.Structural.CollinearMoments

/-! Second-collinear nodes are the first-collinear nodes with wave labels 2 and 3 exchanged. -/
namespace Math.HiggsFourWaveCubature.Structural.SecondCollinear
set_option autoImplicit false
set_option Elab.async false
open scoped BigOperators

def wave : Fin 4 → Fin 4 := ![0,1,3,2]
def index (a : Fin 72) : Fin 72 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            if a.val < 1 then
              0
            else
              1
          else
            if a.val < 3 then
              2
            else
              3
        else
          if a.val < 6 then
            if a.val < 5 then
              4
            else
              5
          else
            if a.val < 7 then
              6
            else
              if a.val < 8 then
                7
              else
                8
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              9
            else
              10
          else
            if a.val < 12 then
              11
            else
              12
        else
          if a.val < 15 then
            if a.val < 14 then
              13
            else
              14
          else
            if a.val < 16 then
              15
            else
              if a.val < 17 then
                16
              else
                17
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            if a.val < 19 then
              18
            else
              19
          else
            if a.val < 21 then
              20
            else
              21
        else
          if a.val < 24 then
            if a.val < 23 then
              22
            else
              23
          else
            if a.val < 25 then
              24
            else
              if a.val < 26 then
                25
              else
                26
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              27
            else
              28
          else
            if a.val < 30 then
              29
            else
              30
        else
          if a.val < 33 then
            if a.val < 32 then
              31
            else
              32
          else
            if a.val < 34 then
              33
            else
              if a.val < 35 then
                34
              else
                35
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          if a.val < 38 then
            if a.val < 37 then
              36
            else
              37
          else
            if a.val < 39 then
              38
            else
              39
        else
          if a.val < 42 then
            if a.val < 41 then
              40
            else
              41
          else
            if a.val < 43 then
              42
            else
              if a.val < 44 then
                43
              else
                44
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              45
            else
              46
          else
            if a.val < 48 then
              47
            else
              48
        else
          if a.val < 51 then
            if a.val < 50 then
              49
            else
              50
          else
            if a.val < 52 then
              51
            else
              if a.val < 53 then
                52
              else
                53
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            if a.val < 55 then
              54
            else
              55
          else
            if a.val < 57 then
              56
            else
              57
        else
          if a.val < 60 then
            if a.val < 59 then
              58
            else
              59
          else
            if a.val < 61 then
              60
            else
              if a.val < 62 then
                61
              else
                62
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              63
            else
              64
          else
            if a.val < 66 then
              65
            else
              66
        else
          if a.val < 69 then
            if a.val < 68 then
              67
            else
              68
          else
            if a.val < 70 then
              69
            else
              if a.val < 71 then
                70
              else
                71

theorem index_involutive : ∀ a : Fin 72, index (index a) = a := by decide +kernel

theorem wave_involutive : ∀ s : Fin 4, wave (wave s) = s := by decide +kernel

theorem raw_transport : ∀ a : Fin 72, ∀ s i : Fin 4,
    raw 1 (index a) s i = raw 2 a (wave s) i := by decide +kernel

theorem gram_transport : ∀ s t : Fin 4,
    gram 1 (wave s) (wave t) = gram 2 s t := by decide +kernel

private def nodeEquiv : Fin 72 ≃ Fin 72 where
  toFun := index
  invFun := index
  left_inv := index_involutive
  right_inv := index_involutive

theorem moment_transport (s t u v i j k l : Fin 4) :
    sumMoment 1 (wave s) (wave t) (wave u) (wave v) i j k l =
      sumMoment 2 s t u v i j k l := by
  have h := Equiv.sum_comp nodeEquiv
    (fun a => raw 1 a (wave s) i*raw 1 a (wave t) j*
      raw 1 a (wave u) k*raw 1 a (wave v) l)
  change (∑ a : Fin 72, raw 1 (index a) (wave s) i*raw 1 (index a) (wave t) j*
    raw 1 (index a) (wave u) k*raw 1 (index a) (wave v) l) =
      sumMoment 1 (wave s) (wave t) (wave u) (wave v) i j k l at h
  rw [←h]
  change _ = ∑ a : Fin 72, raw 2 a s i*raw 2 a t j*raw 2 a u k*raw 2 a v l
  apply Finset.sum_congr rfl
  intro a _
  rw [raw_transport,raw_transport,raw_transport,raw_transport]
  rw [wave_involutive,wave_involutive,wave_involutive,wave_involutive]

theorem second_collinear_moments (s t u v i j k l : Fin 4) :
    sumMoment 2 s t u v i j k l = expected 2 s t u v i j k l := by
  rw [←moment_transport, collinear_moments]
  unfold expected
  simp only [gram_transport]
  rfl
end Math.HiggsFourWaveCubature.Structural.SecondCollinear
