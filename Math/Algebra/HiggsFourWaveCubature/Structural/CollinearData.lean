import Math.Algebra.HiggsFourWaveCubature.Structural.TensorShape

/-! Exact node transports for the unchanged 72-point first-collinear family. -/
namespace Math.HiggsFourWaveCubature.Structural
set_option autoImplicit false

def wick (i : Fin 4) : GaussianInt := if i=0 then 1 else ⟨0,1⟩
def euclid (a : Fin 72) (s i : Fin 4) : GaussianInt := wick i*raw 1 a s i
def phase (p : Fin 4) : GaussianInt := ![1,⟨0,1⟩,-1,⟨0,-1⟩] p

def swapLeft : Fin 6 → Fin 4 := ![0,0,0,1,1,2]
def swapRight : Fin 6 → Fin 4 := ![1,2,3,2,3,3]

def swap01Index (a : Fin 72) : Fin 72 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            if a.val < 1 then
              11
            else
              10
          else
            if a.val < 3 then
              60
            else
              61
        else
          if a.val < 6 then
            if a.val < 5 then
              62
            else
              63
          else
            if a.val < 7 then
              64
            else
              if a.val < 8 then
                65
              else
                66
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              67
            else
              1
          else
            if a.val < 12 then
              0
            else
              51
        else
          if a.val < 15 then
            if a.val < 14 then
              50
            else
              49
          else
            if a.val < 16 then
              48
            else
              if a.val < 17 then
                57
              else
                56
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            if a.val < 19 then
              59
            else
              58
          else
            if a.val < 21 then
              45
            else
              44
        else
          if a.val < 24 then
            if a.val < 23 then
              47
            else
              46
          else
            if a.val < 25 then
              55
            else
              if a.val < 26 then
                54
              else
                53
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              52
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
              42
            else
              43
          else
            if a.val < 39 then
              40
            else
              41
        else
          if a.val < 42 then
            if a.val < 41 then
              38
            else
              39
          else
            if a.val < 43 then
              36
            else
              if a.val < 44 then
                37
              else
                21
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              20
            else
              23
          else
            if a.val < 48 then
              22
            else
              15
        else
          if a.val < 51 then
            if a.val < 50 then
              14
            else
              13
          else
            if a.val < 52 then
              12
            else
              if a.val < 53 then
                27
              else
                26
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            if a.val < 55 then
              25
            else
              24
          else
            if a.val < 57 then
              17
            else
              16
        else
          if a.val < 60 then
            if a.val < 59 then
              19
            else
              18
          else
            if a.val < 61 then
              2
            else
              if a.val < 62 then
                3
              else
                4
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              5
            else
              6
          else
            if a.val < 66 then
              7
            else
              8
        else
          if a.val < 69 then
            if a.val < 68 then
              9
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

def swap01Phase (a : Fin 72) : Fin 4 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            3
          else
            1
        else
          1
      else
        if a.val < 13 then
          if a.val < 11 then
            1
          else
            if a.val < 12 then
              1
            else
              3
        else
          3
    else
      if a.val < 27 then
        3
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              3
            else
              0
          else
            0
        else
          0
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          2
        else
          if a.val < 42 then
            2
          else
            if a.val < 43 then
              2
            else
              if a.val < 44 then
                2
              else
                1
      else
        1
    else
      if a.val < 63 then
        if a.val < 58 then
          1
        else
          if a.val < 60 then
            1
          else
            3
      else
        if a.val < 67 then
          3
        else
          if a.val < 69 then
            if a.val < 68 then
              3
            else
              0
          else
            0

def swap02Index (a : Fin 72) : Fin 72 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            if a.val < 1 then
              67
            else
              66
          else
            if a.val < 3 then
              9
            else
              8
        else
          if a.val < 6 then
            if a.val < 5 then
              68
            else
              69
          else
            if a.val < 7 then
              70
            else
              if a.val < 8 then
                71
              else
                3
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              2
            else
              61
          else
            if a.val < 12 then
              60
            else
              35
        else
          if a.val < 15 then
            if a.val < 14 then
              34
            else
              33
          else
            if a.val < 16 then
              32
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
              54
            else
              55
        else
          if a.val < 24 then
            if a.val < 23 then
              52
            else
              53
          else
            if a.val < 25 then
              37
            else
              if a.val < 26 then
                36
              else
                39
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              38
            else
              57
          else
            if a.val < 30 then
              56
            else
              59
        else
          if a.val < 33 then
            if a.val < 32 then
              58
            else
              15
          else
            if a.val < 34 then
              14
            else
              if a.val < 35 then
                13
              else
                12
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          if a.val < 38 then
            if a.val < 37 then
              25
            else
              24
          else
            if a.val < 39 then
              27
            else
              26
        else
          if a.val < 42 then
            if a.val < 41 then
              47
            else
              46
          else
            if a.val < 43 then
              45
            else
              if a.val < 44 then
                44
              else
                43
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              42
            else
              41
          else
            if a.val < 48 then
              40
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
                22
              else
                23
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            if a.val < 55 then
              20
            else
              21
          else
            if a.val < 57 then
              29
            else
              28
        else
          if a.val < 60 then
            if a.val < 59 then
              31
            else
              30
          else
            if a.val < 61 then
              11
            else
              if a.val < 62 then
                10
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
              1
        else
          if a.val < 69 then
            if a.val < 68 then
              0
            else
              4
          else
            if a.val < 70 then
              5
            else
              if a.val < 71 then
                6
              else
                7

def swap02Phase (a : Fin 72) : Fin 4 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            0
          else
            3
        else
          1
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              1
            else
              2
          else
            if a.val < 12 then
              2
            else
              3
        else
          if a.val < 15 then
            3
          else
            if a.val < 16 then
              3
            else
              0
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            0
          else
            2
        else
          if a.val < 24 then
            2
          else
            1
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              1
            else
              3
          else
            3
        else
          if a.val < 33 then
            if a.val < 32 then
              3
            else
              1
          else
            1
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          3
        else
          if a.val < 42 then
            1
          else
            if a.val < 43 then
              1
            else
              if a.val < 44 then
                1
              else
                3
      else
        if a.val < 49 then
          if a.val < 47 then
            3
          else
            if a.val < 48 then
              3
            else
              0
        else
          if a.val < 51 then
            0
          else
            if a.val < 52 then
              0
            else
              2
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            2
          else
            1
        else
          if a.val < 60 then
            1
          else
            if a.val < 61 then
              2
            else
              if a.val < 62 then
                2
              else
                0
      else
        if a.val < 67 then
          0
        else
          if a.val < 69 then
            if a.val < 68 then
              0
            else
              3
          else
            3

def swap03Index (a : Fin 72) : Fin 72 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            if a.val < 1 then
              65
            else
              64
          else
            if a.val < 3 then
              71
            else
              70
        else
          if a.val < 6 then
            if a.val < 5 then
              7
            else
              6
          else
            if a.val < 7 then
              5
            else
              if a.val < 8 then
                4
              else
                69
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              68
            else
              63
          else
            if a.val < 12 then
              62
            else
              12
        else
          if a.val < 15 then
            if a.val < 14 then
              13
            else
              58
          else
            if a.val < 16 then
              59
            else
              if a.val < 17 then
                35
              else
                34
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            if a.val < 19 then
              37
            else
              36
          else
            if a.val < 21 then
              31
            else
              30
        else
          if a.val < 24 then
            if a.val < 23 then
              41
            else
              40
          else
            if a.val < 25 then
              24
            else
              if a.val < 26 then
                25
              else
                46
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              47
            else
              51
          else
            if a.val < 30 then
              50
            else
              21
        else
          if a.val < 33 then
            if a.val < 32 then
              20
            else
              55
          else
            if a.val < 34 then
              54
            else
              if a.val < 35 then
                17
              else
                16
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          if a.val < 38 then
            if a.val < 37 then
              19
            else
              18
          else
            if a.val < 39 then
              53
            else
              52
        else
          if a.val < 42 then
            if a.val < 41 then
              23
            else
              22
          else
            if a.val < 43 then
              49
            else
              if a.val < 44 then
                48
              else
                44
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              45
            else
              26
          else
            if a.val < 48 then
              27
            else
              43
        else
          if a.val < 51 then
            if a.val < 50 then
              42
            else
              29
          else
            if a.val < 52 then
              28
            else
              if a.val < 53 then
                39
              else
                38
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            if a.val < 55 then
              33
            else
              32
          else
            if a.val < 57 then
              56
            else
              57
        else
          if a.val < 60 then
            if a.val < 59 then
              14
            else
              15
          else
            if a.val < 61 then
              60
            else
              if a.val < 62 then
                61
              else
                11
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              10
            else
              1
          else
            if a.val < 66 then
              0
            else
              66
        else
          if a.val < 69 then
            if a.val < 68 then
              67
            else
              9
          else
            if a.val < 70 then
              8
            else
              if a.val < 71 then
                3
              else
                2

def swap03Phase (a : Fin 72) : Fin 4 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          0
        else
          if a.val < 6 then
            3
          else
            if a.val < 7 then
              1
            else
              if a.val < 8 then
                1
              else
                2
      else
        if a.val < 13 then
          if a.val < 11 then
            2
          else
            if a.val < 12 then
              2
            else
              0
        else
          if a.val < 15 then
            if a.val < 14 then
              0
            else
              2
          else
            if a.val < 16 then
              2
            else
              3
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            1
          else
            3
        else
          if a.val < 24 then
            1
          else
            if a.val < 25 then
              0
            else
              if a.val < 26 then
                0
              else
                2
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              2
            else
              3
          else
            if a.val < 30 then
              3
            else
              1
        else
          if a.val < 33 then
            if a.val < 32 then
              1
            else
              3
          else
            if a.val < 34 then
              3
            else
              1
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          if a.val < 38 then
            3
          else
            1
        else
          if a.val < 42 then
            3
          else
            if a.val < 43 then
              1
            else
              if a.val < 44 then
                1
              else
                0
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              0
            else
              2
          else
            if a.val < 48 then
              2
            else
              3
        else
          if a.val < 51 then
            if a.val < 50 then
              3
            else
              1
          else
            if a.val < 52 then
              1
            else
              3
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            1
          else
            0
        else
          if a.val < 60 then
            2
          else
            if a.val < 61 then
              0
            else
              if a.val < 62 then
                0
              else
                2
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              2
            else
              0
          else
            0
        else
          if a.val < 69 then
            if a.val < 68 then
              0
            else
              2
          else
            if a.val < 70 then
              2
            else
              0

def swap12Index (a : Fin 72) : Fin 72 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            if a.val < 1 then
              2
            else
              3
          else
            if a.val < 3 then
              0
            else
              1
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
                10
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              11
            else
              8
          else
            if a.val < 12 then
              9
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
                28
              else
                29
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            if a.val < 19 then
              30
            else
              31
          else
            if a.val < 21 then
              36
            else
              37
        else
          if a.val < 24 then
            if a.val < 23 then
              38
            else
              39
          else
            if a.val < 25 then
              44
            else
              if a.val < 26 then
                45
              else
                46
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              47
            else
              16
          else
            if a.val < 30 then
              17
            else
              18
        else
          if a.val < 33 then
            if a.val < 32 then
              19
            else
              48
          else
            if a.val < 34 then
              49
            else
              if a.val < 35 then
                50
              else
                51
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          if a.val < 38 then
            if a.val < 37 then
              20
            else
              21
          else
            if a.val < 39 then
              22
            else
              23
        else
          if a.val < 42 then
            if a.val < 41 then
              52
            else
              53
          else
            if a.val < 43 then
              54
            else
              if a.val < 44 then
                55
              else
                24
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              25
            else
              26
          else
            if a.val < 48 then
              27
            else
              32
        else
          if a.val < 51 then
            if a.val < 50 then
              33
            else
              34
          else
            if a.val < 52 then
              35
            else
              if a.val < 53 then
                40
              else
                41
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            if a.val < 55 then
              42
            else
              43
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
              67
            else
              if a.val < 62 then
                66
              else
                68
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              69
            else
              70
          else
            if a.val < 66 then
              71
            else
              61
        else
          if a.val < 69 then
            if a.val < 68 then
              60
            else
              62
          else
            if a.val < 70 then
              63
            else
              if a.val < 71 then
                64
              else
                65

def swap12Phase (a : Fin 72) : Fin 4 :=
  if a.val < 36 then
    0
  else
    if a.val < 54 then
      0
    else
      if a.val < 63 then
        if a.val < 58 then
          0
        else
          if a.val < 60 then
            0
          else
            if a.val < 61 then
              3
            else
              if a.val < 62 then
                3
              else
                0
      else
        if a.val < 67 then
          if a.val < 65 then
            0
          else
            if a.val < 66 then
              0
            else
              1
        else
          if a.val < 69 then
            if a.val < 68 then
              1
            else
              0
          else
            0

def swap13Index (a : Fin 72) : Fin 72 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            if a.val < 1 then
              4
            else
              5
          else
            if a.val < 3 then
              2
            else
              3
        else
          if a.val < 6 then
            if a.val < 5 then
              0
            else
              1
          else
            if a.val < 7 then
              10
            else
              if a.val < 8 then
                11
              else
                8
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              9
            else
              6
          else
            if a.val < 12 then
              7
            else
              28
        else
          if a.val < 15 then
            if a.val < 14 then
              29
            else
              36
          else
            if a.val < 16 then
              37
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
              48
            else
              49
          else
            if a.val < 21 then
              20
            else
              21
        else
          if a.val < 24 then
            if a.val < 23 then
              52
            else
              53
          else
            if a.val < 25 then
              32
            else
              if a.val < 26 then
                33
              else
                40
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              41
            else
              12
          else
            if a.val < 30 then
              13
            else
              44
        else
          if a.val < 33 then
            if a.val < 32 then
              45
            else
              24
          else
            if a.val < 34 then
              25
            else
              if a.val < 35 then
                56
              else
                57
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          if a.val < 38 then
            if a.val < 37 then
              14
            else
              15
          else
            if a.val < 39 then
              46
            else
              47
        else
          if a.val < 42 then
            if a.val < 41 then
              26
            else
              27
          else
            if a.val < 43 then
              58
            else
              if a.val < 44 then
                59
              else
                30
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              31
            else
              38
          else
            if a.val < 48 then
              39
            else
              18
        else
          if a.val < 51 then
            if a.val < 50 then
              19
            else
              50
          else
            if a.val < 52 then
              51
            else
              if a.val < 53 then
                22
              else
                23
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
              34
            else
              35
        else
          if a.val < 60 then
            if a.val < 59 then
              42
            else
              43
          else
            if a.val < 61 then
              71
            else
              if a.val < 62 then
                70
              else
                65
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              64
            else
              63
          else
            if a.val < 66 then
              62
            else
              69
        else
          if a.val < 69 then
            if a.val < 68 then
              68
            else
              67
          else
            if a.val < 70 then
              66
            else
              if a.val < 71 then
                61
              else
                60

def swap13Phase (a : Fin 72) : Fin 4 :=
  if a.val < 36 then
    0
  else
    if a.val < 54 then
      0
    else
      if a.val < 63 then
        if a.val < 58 then
          0
        else
          if a.val < 60 then
            0
          else
            3
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              3
            else
              1
          else
            1
        else
          if a.val < 69 then
            if a.val < 68 then
              1
            else
              3
          else
            if a.val < 70 then
              3
            else
              1

def swap23Index (a : Fin 72) : Fin 72 :=
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
              4
            else
              5
        else
          if a.val < 6 then
            if a.val < 5 then
              2
            else
              3
          else
            if a.val < 7 then
              8
            else
              if a.val < 8 then
                9
              else
                6
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              7
            else
              10
          else
            if a.val < 12 then
              11
            else
              16
        else
          if a.val < 15 then
            if a.val < 14 then
              17
            else
              20
          else
            if a.val < 16 then
              21
            else
              if a.val < 17 then
                12
              else
                13
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            if a.val < 19 then
              24
            else
              25
          else
            if a.val < 21 then
              14
            else
              15
        else
          if a.val < 24 then
            if a.val < 23 then
              26
            else
              27
          else
            if a.val < 25 then
              18
            else
              if a.val < 26 then
                19
              else
                22
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              23
            else
              28
          else
            if a.val < 30 then
              29
            else
              32
        else
          if a.val < 33 then
            if a.val < 32 then
              33
            else
              30
          else
            if a.val < 34 then
              31
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
              40
            else
              41
        else
          if a.val < 42 then
            if a.val < 41 then
              38
            else
              39
          else
            if a.val < 43 then
              42
            else
              if a.val < 44 then
                43
              else
                48
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              49
            else
              52
          else
            if a.val < 48 then
              53
            else
              44
        else
          if a.val < 51 then
            if a.val < 50 then
              45
            else
              56
          else
            if a.val < 52 then
              57
            else
              if a.val < 53 then
                46
              else
                47
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            if a.val < 55 then
              58
            else
              59
          else
            if a.val < 57 then
              50
            else
              51
        else
          if a.val < 60 then
            if a.val < 59 then
              54
            else
              55
          else
            if a.val < 61 then
              62
            else
              if a.val < 62 then
                63
              else
                60
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              61
            else
              66
          else
            if a.val < 66 then
              67
            else
              64
        else
          if a.val < 69 then
            if a.val < 68 then
              65
            else
              71
          else
            if a.val < 70 then
              70
            else
              if a.val < 71 then
                69
              else
                68

def swap23Phase (a : Fin 72) : Fin 4 :=
  if a.val < 36 then
    0
  else
    if a.val < 54 then
      0
    else
      if a.val < 63 then
        0
      else
        if a.val < 67 then
          0
        else
          if a.val < 69 then
            if a.val < 68 then
              0
            else
              3
          else
            if a.val < 70 then
              3
            else
              1

def hadamardIndex (a : Fin 72) : Fin 72 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            if a.val < 1 then
              50
            else
              51
          else
            if a.val < 3 then
              34
            else
              35
        else
          if a.val < 6 then
            if a.val < 5 then
              56
            else
              57
          else
            if a.val < 7 then
              13
            else
              if a.val < 8 then
                12
              else
                29
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              28
            else
              17
          else
            if a.val < 12 then
              16
            else
              7
        else
          if a.val < 15 then
            if a.val < 14 then
              6
            else
              59
          else
            if a.val < 16 then
              58
            else
              if a.val < 17 then
                11
              else
                10
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            if a.val < 19 then
              30
            else
              31
          else
            if a.val < 21 then
              43
            else
              42
        else
          if a.val < 24 then
            if a.val < 23 then
              71
            else
              70
          else
            if a.val < 25 then
              44
            else
              if a.val < 26 then
                45
              else
                60
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              61
            else
              9
          else
            if a.val < 30 then
              8
            else
              18
        else
          if a.val < 33 then
            if a.val < 32 then
              19
            else
              48
          else
            if a.val < 34 then
              49
            else
              if a.val < 35 then
                2
              else
                3
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          if a.val < 38 then
            if a.val < 37 then
              55
            else
              54
          else
            if a.val < 39 then
              65
            else
              64
        else
          if a.val < 42 then
            if a.val < 41 then
              62
            else
              63
          else
            if a.val < 43 then
              21
            else
              if a.val < 44 then
                20
              else
                24
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              25
            else
              67
          else
            if a.val < 48 then
              66
            else
              32
        else
          if a.val < 51 then
            if a.val < 50 then
              33
            else
              0
          else
            if a.val < 52 then
              1
            else
              if a.val < 53 then
                68
              else
                69
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            if a.val < 55 then
              37
            else
              36
          else
            if a.val < 57 then
              4
            else
              5
        else
          if a.val < 60 then
            if a.val < 59 then
              15
            else
              14
          else
            if a.val < 61 then
              26
            else
              if a.val < 62 then
                27
              else
                40
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              41
            else
              39
          else
            if a.val < 66 then
              38
            else
              47
        else
          if a.val < 69 then
            if a.val < 68 then
              46
            else
              52
          else
            if a.val < 70 then
              53
            else
              if a.val < 71 then
                23
              else
                22

def hadamardPhase (a : Fin 72) : Fin 4 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          0
        else
          if a.val < 6 then
            0
          else
            1
      else
        if a.val < 13 then
          if a.val < 11 then
            1
          else
            if a.val < 12 then
              1
            else
              3
        else
          3
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            0
          else
            3
        else
          if a.val < 24 then
            0
          else
            if a.val < 25 then
              0
            else
              if a.val < 26 then
                0
              else
                1
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              1
            else
              3
          else
            if a.val < 30 then
              3
            else
              0
        else
          0
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          if a.val < 38 then
            3
          else
            0
        else
          if a.val < 42 then
            1
          else
            if a.val < 43 then
              1
            else
              if a.val < 44 then
                1
              else
                0
      else
        if a.val < 49 then
          0
        else
          if a.val < 51 then
            0
          else
            if a.val < 52 then
              0
            else
              1
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            1
          else
            0
        else
          if a.val < 60 then
            1
          else
            3
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              3
            else
              0
          else
            0
        else
          if a.val < 69 then
            if a.val < 68 then
              0
            else
              3
          else
            if a.val < 70 then
              3
            else
              0

def swapIndex (m : Fin 6) : Fin 72 → Fin 72 :=
  ![swap01Index,swap02Index,swap03Index,swap12Index,swap13Index,swap23Index] m

def swapPhase (m : Fin 6) : Fin 72 → Fin 4 :=
  ![swap01Phase,swap02Phase,swap03Phase,swap12Phase,swap13Phase,swap23Phase] m

def gramPositive (a : Fin 72) : Bool :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            if a.val < 1 then
              true
            else
              false
          else
            if a.val < 3 then
              true
            else
              false
        else
          if a.val < 6 then
            if a.val < 5 then
              true
            else
              false
          else
            if a.val < 7 then
              true
            else
              if a.val < 8 then
                false
              else
                true
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              false
            else
              true
          else
            if a.val < 12 then
              false
            else
              true
        else
          if a.val < 15 then
            if a.val < 14 then
              false
            else
              true
          else
            if a.val < 16 then
              false
            else
              if a.val < 17 then
                true
              else
                false
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            if a.val < 19 then
              true
            else
              false
          else
            if a.val < 21 then
              true
            else
              false
        else
          if a.val < 24 then
            if a.val < 23 then
              true
            else
              false
          else
            if a.val < 25 then
              true
            else
              if a.val < 26 then
                false
              else
                true
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              false
            else
              true
          else
            if a.val < 30 then
              false
            else
              true
        else
          if a.val < 33 then
            if a.val < 32 then
              false
            else
              true
          else
            if a.val < 34 then
              false
            else
              if a.val < 35 then
                true
              else
                false
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          if a.val < 38 then
            if a.val < 37 then
              true
            else
              false
          else
            if a.val < 39 then
              true
            else
              false
        else
          if a.val < 42 then
            if a.val < 41 then
              true
            else
              false
          else
            if a.val < 43 then
              true
            else
              if a.val < 44 then
                false
              else
                true
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              false
            else
              true
          else
            if a.val < 48 then
              false
            else
              true
        else
          if a.val < 51 then
            if a.val < 50 then
              false
            else
              true
          else
            if a.val < 52 then
              false
            else
              if a.val < 53 then
                true
              else
                false
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            if a.val < 55 then
              true
            else
              false
          else
            if a.val < 57 then
              true
            else
              false
        else
          if a.val < 60 then
            if a.val < 59 then
              true
            else
              false
          else
            if a.val < 61 then
              false
            else
              if a.val < 62 then
                true
              else
                false
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              true
            else
              false
          else
            if a.val < 66 then
              true
            else
              false
        else
          if a.val < 69 then
            if a.val < 68 then
              true
            else
              false
          else
            if a.val < 70 then
              true
            else
              if a.val < 71 then
                false
              else
                true

def gramSign (a : Fin 72) : GaussianInt := if gramPositive a then 1 else -1
end Math.HiggsFourWaveCubature.Structural
